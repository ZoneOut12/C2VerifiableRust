import sys, os, re
from enum import Enum
from antlr4 import InputStream, CommonTokenStream
from antlr4.ListTokenSource import ListTokenSource
from antlr4.Token import Token
from antlr4.error.ErrorListener import ErrorListener
from src.analysis.type_analysis import RustTypeAnalyzer
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from src.acsl.rewrite import ACSLRewriter
from src.spec.acslitem import NonTypedItemExtractor
from src.spec.taint2sink import Taint2Sink


class ExitEarly(Exception):
    pass


class MyErrorListener(ErrorListener):
    def __init__(self):
        self.has_error = False

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        self.has_error = True


class TransformError(Enum):
    Others = 0
    At = 1
    InductiveDef = 2
    AxiomaticDecl = 3
    UnsupportedType = 4
    ReadsClause = 5
    TerminatesClause = 6
    ParamIsPointerType = 7
    Labels = 8
    GhostCode = 9


class ACSLFunctionSignature:
    def __init__(self, param_types):
        self.param_types = param_types  # e.g., ["int", "int"]

    def __repr__(self):
        return f"({', '.join(self.param_types)})"


class SliceDetector(ACSLParserVisitor):
    def __init__(self):
        super().__init__()
        self.sliceIdent = []
        self.detecting = False
        self.is_in_valid = False

        # In face of calling logic predicate and functions.
        self.logic_func_slice_params = {}
        self.cur_logic_func_param_names = []

    def cache(self, logic_func_slice_params, cur_logic_func_param_names):
        self.logic_func_slice_params = logic_func_slice_params
        self.cur_logic_func_param_names = cur_logic_func_param_names

    def clean(self):
        self.sliceIdent = []

    def visitTerm(self, ctx):
        if self.detecting == True:
            # term: '*' term
            if ctx.LPAR() and ctx.RPAR() and ctx.term() and len(ctx.children) == 3:
                self.visitTerm(ctx.term()[0])
            elif ctx.ADD() or ctx.MINUS():
                IDENT_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9_]*$")
                for child in ctx.children:
                    if bool(IDENT_RE.match(child.getText())) == True:
                        self.sliceIdent.append(child.getText())
            return
        if ctx.LBRACKET() and ctx.RBRACKET() and not ctx.WITH():
            # term: term '[' term ']'
            self.sliceIdent.append(self.visit(ctx.term()[0]))
        elif ctx.MUL() and len(ctx.term()) == 1:
            # term: '*' term
            self.detecting = True
            self.visitTerm(ctx.term()[0])
            self.detecting = False
        elif ctx.polyId():
            called_logic_func_name = self.visit(ctx.polyId())

            if self.logic_func_slice_params.get(called_logic_func_name) is not None:
                slice_param_ids = self.logic_func_slice_params.get(
                    called_logic_func_name
                )
                for index in slice_param_ids:
                    if (
                        self.visit(ctx.term()[index]).strip()
                        in self.cur_logic_func_param_names
                    ):
                        self.sliceIdent.append(self.visit(ctx.term()[index]))

        return self.visitChildren(ctx)

    def visitPred(self, ctx):
        if ctx.VALID() or ctx.VALIDREAD():
            self.is_in_valid = True
            res = self.visitChildren(ctx)
            self.is_in_valid = False
            return res
        return self.visitChildren(ctx)

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitTerminal(self, node):
        if self.is_in_valid:
            token = node.getSymbol()
            token_type = token.type
            if token_type == ACSLLexer.IDENT:
                self.sliceIdent.append(node.getText())
        return node.getText()


class ACSL2Verus(ACSLParserVisitor):
    """
    Currently, just support a subset of ACSL.
    """

    def __init__(self, file_path, lang_lib, logger, type_guidance):
        super().__init__()
        self.lang_lib = lang_lib
        self.logger = logger
        self.return_code = 0
        self.error_type = None
        self.file_path = file_path
        self.is_in_range = False
        self.function_table = {}
        self.slicedetector = SliceDetector()
        self.is_in_logic_func = False
        # pred: '!' pred
        self.negation = 0
        # term: '*' term
        # tset: '*' tset
        self.dereference = 0
        self.cached_typed_items = []
        self.cur_comment_id = 0
        self.is_in_old_logic_func = False

        # count eliminated specific specifications
        self.eliminated_specs = {}

        self.type_guided = type_guidance
        self.ghost_function_type_guided = type_guidance

        # recode logic function sequential order, to process slice type
        self.logic_func_slice_params = {}
        self.cur_logic_func_param_names = []
        # `self.logicfuncname_to_sliceparamid_map = {}` same as `self.logic_func_slice_params`

        # record the broadcast lemmas introduced during migrating inductive definitions
        self.broadcast_inductive_lemmas = []

        # call RustTypeAnalysis to execute type-guided specification migration
        self.type_guidance_args = {}

    def get_eliminated_spec(self):
        res = self.eliminated_specs.copy()
        self.eliminated_specs.clear()
        return res

    def updata_cached_typed_items(self, typed_items):
        self.cached_typed_items = typed_items

    def extract_types_in_formal_params(self, input_str):
        # refined regex to match Rust types, including reference types like &[]
        pattern = (
            r":\s*([a-zA-Z_][a-zA-Z0-9_]*\s*(?:<[^>]+>)?|\&\[[a-zA-Z_][a-zA-Z0-9_]*\])"
        )
        types = re.findall(pattern, input_str)
        return types

    def extract_params_names_in_formal_params(self, input_str):
        # use regex to match parameter names part
        pattern = r"([a-zA-Z_][a-zA-Z0-9_]*)\s*:"
        params = re.findall(pattern, input_str)

        return params

    def logger_ctx_debug_info(self, ctx, error_msg):
        """
        Get the debug information of the context.
        """
        start_token = ctx.start
        start_line = start_token.line
        start_column = start_token.column
        self.logger.error(
            f'File "{self.file_path}", line {start_line}, column {start_column}:\n{error_msg}'
        )
        return start_line, start_column

    def visitAcsl(self, ctx):
        if ctx.funcContract():
            return self.visitFuncContract(ctx.funcContract())
        elif ctx.cStatement():
            return self.visitCStatement(ctx.cStatement())
        elif ctx.cExternalDeclaration():
            return self.visitCExternalDeclaration(ctx.cExternalDeclaration())
        else:
            return ""

    def visitCStatement(self, ctx):
        """
        cStatement:
            '/*@' loopAnnot '*/'
            | '//@' loopAnnot LINEEND
            | assertion;
        """
        if ctx.loopAnnot():
            return self.visitLoopAnnot(ctx.loopAnnot())
        elif ctx.assertion():
            return self.visitAssertion(ctx.assertion())
        else:
            return self.visitChildren(ctx)

    def visitFuncContract(self, ctx):
        verus_code = str()
        is_first = True
        for clause in ctx.requiresClause():
            if self.visitRequiresClause(clause).strip() != "":
                if is_first:
                    verus_code += "requires\n\t"
                    verus_code += self.visitRequiresClause(clause)
                    verus_code += ",\n"
                    is_first = False
                else:
                    verus_code += "\t" + self.visitRequiresClause(clause)
                    verus_code += ",\n"
        is_first = True
        for clause in ctx.simpleClause():
            if clause.ensuresClause():
                if self.visitEnsuresClause(clause.ensuresClause()).strip() != "":
                    if is_first:
                        is_first = False
                        verus_code += "ensures\n\t"
                        verus_code += self.visitEnsuresClause(clause.ensuresClause())
                        verus_code += ",\n"
                    else:
                        verus_code += "\t" + self.visitEnsuresClause(
                            clause.ensuresClause()
                        )
                        verus_code += ",\n"
        for behavior in ctx.namedBehavior():
            if is_first:
                is_first = False
                verus_code += "ensures\n\t"
                verus_code += self.visitNamedBehavior(behavior)
                verus_code += ",\n"
            else:
                verus_code += "\t" + self.visitNamedBehavior(behavior)
                verus_code += ",\n"
        if ctx.decreasesClause():
            verus_code += self.visitDecreasesClause(ctx.decreasesClause()) + "\n"

        return verus_code.strip()

    def visitAssertion(self, ctx):
        pred = self.visit(ctx.pred())
        return "assert(" + pred + ");"

    def visitLoopAnnot(self, ctx):
        # loopAnnot = self.visitChildren(ctx)
        invariant_count = 0
        verus_code = ""
        for clause in ctx.loopClause():
            if clause.loopInvariant():
                invclause = clause.loopInvariant()
                invariant_count += 1
                invariant = self.visit(invclause)
                if invariant_count == 1:
                    verus_code += "invariant\n"
                    verus_code += "\t" + self.visit(invclause.pred()) + ",\n"
                else:
                    verus_code += "\t" + self.visit(invclause.pred()) + ",\n"
        if ctx.loopVariant():
            return verus_code.strip() + "\n" + self.visit(ctx.loopVariant())
        else:
            return verus_code.strip()

    def visitAssignsClause(self, ctx):
        """eliminate 'assign' clause in Verus, so return empty string"""
        if self.eliminated_specs.get("assigns") is None:
            self.eliminated_specs["assigns"] = 0
        self.eliminated_specs["assigns"] += 1
        # return "flag_assigns"
        return ""

    def visitEnsuresClause(self, ctx):
        # ensuresClause: 'ensures' pred ';';
        # return self.visitChildren(ctx) + "\n"
        return self.visit(ctx.pred())

    def visitRequiresClause(self, ctx):
        # requiresClause: 'requires' pred ';';
        # return self.visitChildren(ctx) + "\n"
        if self.type_guided:
            self.is_in_old_logic_func = True
            res = self.visit(ctx.pred())
            self.is_in_old_logic_func = False
            return res
        else:
            return self.visit(ctx.pred())

    def visitTset(self, ctx):
        if ctx.LBRACE() and ctx.RBRACE():
            # tset: '{' ( term (',' term)*)? '}';
            return "set!" + self.visitChildren(ctx)
        elif ctx.LBRACKET() and ctx.RBRACKET() and not ctx.range_():
            # tset: tset '[' tset ']';
            return (
                self.visit(ctx.tset()[0])
                + "@[("
                + self.visit(ctx.tset()[1])
                + ") as int]"
            )
        elif ctx.LBRACKET() and ctx.RBRACKET() and ctx.range_():
            # tset: tset '[' range ']';
            return self.visit(ctx.tset()[0]) + "@[" + self.visit(ctx.range_()) + "]"
            # return self.visitChildren(ctx)
        ###
        elif ctx.MUL() and ctx.getChildCount() == 2:
            # tset: '*' tset
            if self.dereference > 0:
                self.dereference -= 1
                deref_item = self.visitTset(ctx.tset()[0])
                if self.type_guided:
                    non_typed_item_extracter = NonTypedItemExtractor(
                        self.lang_lib, self.logger
                    )
                    non_typed_deref_item = non_typed_item_extracter.visit(ctx.tset()[0])
                    for item in self.cached_typed_items:
                        if item[
                            "index"
                        ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                            item
                        ):
                            for param in item["items"]:
                                if param["name"] == ctx.tset()[0].getText().strip():
                                    deref_item_type = param["type"]
                                    if RustTypeAnalyzer.is_type_option(deref_item_type):
                                        return "(" + deref_item + ").unwrap()@"
                                    else:
                                        return "(" + deref_item + ")@"
                        elif item[
                            "index"
                        ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                            item
                        ):
                            if item["item"] == non_typed_deref_item.strip():
                                deref_item_type = item["type"]
                                if RustTypeAnalyzer.is_type_option(deref_item_type):
                                    return "(" + deref_item + ").unwrap()@"
                                else:
                                    return "(" + deref_item + ")@"
                    return "(" + deref_item + ")@"
                else:
                    return "*(" + deref_item + ")"
            text = ctx.getText()
            input_stream = InputStream(text)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            token_stream.fill()
            num_tokens = len(token_stream.tokens)
            for end in range(num_tokens - 1):
                sub_tokens = token_stream.tokens[: (end + 2)]
                # sub_tokens.append(CommonToken(type=Token.EOF, text="<EOF>"))
                sub_token_source = ListTokenSource(sub_tokens)
                sub_token_stream = CommonTokenStream(sub_token_source)
                acsl_parser = ACSLParser(sub_token_stream)
                listener = MyErrorListener()
                acsl_parser.removeErrorListeners()
                acsl_parser.addErrorListener(listener)
                tree = acsl_parser.tset()
                # self.logger.error(f"term: '*' term\n{tree.getText()}\n{type(tree)}")
                if listener.has_error:
                    continue
                else:
                    new_text = (
                        "( "
                        + " ".join(
                            tok.text for tok in sub_tokens if tok.type != Token.EOF
                        )
                        + " ) "
                    )
                    new_text += " ".join(
                        tok.text
                        for tok in token_stream.tokens[(end + 2) :]
                        if tok.type != Token.EOF
                    )
                    new_input_stream = InputStream(new_text)
                    new_lexer = ACSLLexer(new_input_stream)
                    new_token_stream = CommonTokenStream(new_lexer)
                    new_acsl_parser = ACSLParser(new_token_stream)
                    new_term = new_acsl_parser.tset()
                    self.dereference += 1
                    return self.visitTset(new_term)
            self.logger.error(
                f"Error occurred in **ACSL2Verus.visitTset** method!\n{ctx.getText()}\n"
            )
            raise ValueError(
                f"Error occurred in **ACSL2Verus.visitTset** method!\n{ctx.getText()}\n"
            )
        ###
        else:
            return self.visitChildren(ctx)

    def visitRange(self, ctx):
        # range: term? '..' term?;
        self.is_in_range = True
        res = ""
        for child in ctx.children:
            if isinstance(child, ACSLParser.TermContext):
                res += r"((" + self.visitTerm(child) + r") as int)"
            else:
                res += self.visit(child)
        self.is_in_range = False
        return res

    def visitTerm(self, ctx):
        if ctx.AT():
            error_msg = f"{ctx.getText()} has '\\at' which cannnot be transformed."
            self.logger_ctx_debug_info(ctx, error_msg=error_msg)
            self.error_type = TransformError.At
            self.return_code = -1
            raise ExitEarly(
                f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
            )
        ###
        elif ctx.OLD():
            if self.type_guided:
                self.is_in_old_logic_func = True
                res = self.visit(ctx.term()[0])
                self.is_in_old_logic_func = False
                return res
            else:
                return "old(" + self.visit(ctx.term()[0]) + ")"
        elif ctx.MUL() and ctx.getChildCount() == 2:
            # term: '*' term
            if self.dereference > 0:
                self.dereference -= 1
                deref_item = self.visitTerm(ctx.term()[0])
                if self.type_guided:
                    non_typed_item_extracter = NonTypedItemExtractor(
                        lang_lib=self.lang_lib, logger=self.logger
                    )
                    non_typed_deref_item = non_typed_item_extracter.visit(ctx.term()[0])
                    for item in self.cached_typed_items:
                        if item[
                            "index"
                        ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                            item
                        ):
                            for param in item["items"]:
                                if param["name"] == ctx.term()[0].getText().strip():
                                    deref_item_type = param["type"]
                                    if RustTypeAnalyzer.is_type_option(deref_item_type):
                                        return "(" + deref_item + ").unwrap()@"
                                    else:
                                        return "(" + deref_item + ")@"
                        elif item[
                            "index"
                        ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                            item
                        ):
                            if item["item"] == non_typed_deref_item.strip():
                                deref_item_type = item["type"]
                                if RustTypeAnalyzer.is_type_option(deref_item_type):
                                    return "(" + deref_item + ").unwrap()@"
                                else:
                                    return "(" + deref_item + ")@"
                    return "(" + deref_item + r")@"
                else:
                    return "*(" + deref_item + ")"
            text = ctx.getText()
            input_stream = InputStream(text)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            token_stream.fill()
            num_tokens = len(token_stream.tokens)
            for end in range(num_tokens - 1):
                sub_tokens = token_stream.tokens[: (end + 2)]
                # sub_tokens.append(CommonToken(type=Token.EOF, text="<EOF>"))
                sub_token_source = ListTokenSource(sub_tokens)
                sub_token_stream = CommonTokenStream(sub_token_source)
                acsl_parser = ACSLParser(sub_token_stream)
                listener = MyErrorListener()
                acsl_parser.removeErrorListeners()
                acsl_parser.addErrorListener(listener)
                tree = acsl_parser.term()
                # self.logger.error(f"term: '*' term\n{tree.getText()}\n{type(tree)}")
                if listener.has_error:
                    continue
                else:
                    new_text = (
                        "( "
                        + " ".join(
                            tok.text for tok in sub_tokens if tok.type != Token.EOF
                        )
                        + " ) "
                    )
                    new_text += " ".join(
                        tok.text
                        for tok in token_stream.tokens[(end + 2) :]
                        if tok.type != Token.EOF
                    )
                    new_input_stream = InputStream(new_text)
                    new_lexer = ACSLLexer(new_input_stream)
                    new_token_stream = CommonTokenStream(new_lexer)
                    new_acsl_parser = ACSLParser(new_token_stream)
                    new_term = new_acsl_parser.term()
                    self.dereference += 1
                    return self.visitTerm(new_term)
            self.logger.error(
                f"Error occurred in **ACSL2Verus.visitTerm** method!\n{ctx.getText()}\n"
            )
            raise ValueError(
                f"Error occurred in **ACSL2Verus.visitTerm** method!\n{ctx.getText()}\n"
            )
        ###
        elif ctx.NULL():
            if ctx.EQ():
                return "(" + self.visit(ctx.term()[0]) + ").is_none()"
            else:
                return "(" + self.visit(ctx.term()[0]) + ").is_some()"
        elif ctx.LBRACKET() and ctx.RBRACKET() and not ctx.WITH():
            # term: term '[' term ']';
            # slice index type should be `int`` in Verus specification.
            return (
                self.visit(ctx.term()[0])
                + "@[("
                + self.visit(ctx.term()[1])
                + ") as int]"
            )
        elif ctx.ABS():
            return "abs((" + self.visit(ctx.term()[0]) + ") as int)"
        elif ctx.LBRACE() and ctx.RBRACE() and not ctx.WITH():
            # term: '{' term (',' term)* '}';
            return "set!" + self.visitChildren(ctx)
        elif ctx.ARROW():
            # term '->' IDENT
            return self.visit(ctx.term()[0]) + "." + self.visit(ctx.IDENT())
        elif ctx.QUESTIONMARK():
            # term: term '?' term ':' term;
            return (
                "if "
                + self.visit(ctx.term()[0])
                + " { "
                + self.visit(ctx.term()[1])
                + " } else { "
                + self.visit(ctx.term()[2])
                + " }"
            )
        elif ctx.polyId():
            # polyId '(' term (',' term)* ')'
            # check formal parameter types and add type coercion as appropriate
            func_name = self.visit(ctx.polyId().id_().IDENT())
            if func_name == "strlen":
                return "((" + self.visit(ctx.term()[0]) + ")@.len() - 1)"
            if not self.ghost_function_type_guided:
                res = ""
                for child in ctx.children:
                    res += self.visit(child)
                return res
            if func_name in self.function_table:
                param_types = self.function_table[func_name].param_types
                res = ""
                param_order = 0
                for child in ctx.children:
                    if isinstance(child, ACSLParser.TermContext):
                        if param_types[param_order] != None:
                            res += self.visit(child) + " as " + param_types[param_order]
                        else:
                            res += self.visit(child)
                        param_order += 1
                    else:
                        res += self.visit(child)
                return res
            else:
                return self.visitChildren(ctx)
        else:
            return self.visitChildren(ctx)

    def visitPred(self, ctx):
        # pred = self.visitChildren(ctx).strip()
        if ctx.IDENT() and ctx.COLON():
            # pred: IDENT ':' pred;
            # return "((" + self.visit(ctx.pred()[0]) + ") as int != 0)"
            return self.visit(ctx.pred()[0])
        if ctx.NEG():
            if self.negation > 0:
                self.negation -= 1
                pred = self.visit(ctx.pred()[0])
                return "!((" + pred + ") as int != 0)"
            text = ctx.getText()
            input_stream = InputStream(text)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            token_stream.fill()
            num_tokens = len(token_stream.tokens)
            for end in range(num_tokens - 1):
                sub_tokens = token_stream.tokens[: (end + 2)]
                sub_token_source = ListTokenSource(sub_tokens)
                sub_token_stream = CommonTokenStream(sub_token_source)
                acsl_parser = ACSLParser(sub_token_stream)
                listener = MyErrorListener()
                acsl_parser.removeErrorListeners()
                acsl_parser.addErrorListener(listener)
                tree = acsl_parser.pred()

                if listener.has_error:
                    continue
                else:
                    new_text = (
                        "( "
                        + " ".join(
                            tok.text for tok in sub_tokens if tok.type != Token.EOF
                        )
                        + " ) "
                    )
                    new_text += " ".join(
                        tok.text
                        for tok in token_stream.tokens[(end + 2) :]
                        if tok.type != Token.EOF
                    )
                    new_input_stream = InputStream(new_text)
                    new_lexer = ACSLLexer(new_input_stream)
                    new_token_stream = CommonTokenStream(new_lexer)
                    new_acsl_parser = ACSLParser(new_token_stream)
                    new_pred = new_acsl_parser.pred()
                    self.negation += 1
                    return self.visit(new_pred)
            pred = self.visit(ctx.pred()[0])
            return "!((" + pred + ") as int != 0)"
        elif ctx.IMPLY():
            # handle: expected bool, found integer.
            pred1 = self.visit(ctx.pred()[0])
            pred2 = self.visit(ctx.pred()[1])
            return "(" + pred1 + ") as int != 0 ==> (" + pred2 + ") as int != 0"
        elif ctx.EQUIV():
            # handle: expected bool, found integer.
            pred1 = self.visit(ctx.pred()[0])
            pred2 = self.visit(ctx.pred()[1])
            return "(" + pred1 + ") as int != 0 <==> (" + pred2 + ") as int != 0"
        elif ctx.IN():
            # pred: term '\\in' tset;
            return (
                self.visit(ctx.tset()[0])
                + ".contains("
                + self.visit(ctx.term()[0])
                + ")"
            )
        elif ctx.NULL():
            if ctx.EQ():
                return "(" + self.visit(ctx.term()[0]) + ").is_none()"
            else:
                return "(" + self.visit(ctx.term()[0]) + ").is_some()"
        elif ctx.SEPARATED():
            # pred: '\\separated' '(' location ',' locationsList ')';
            if self.eliminated_specs.get("separated") is None:
                self.eliminated_specs["separated"] = 0
            self.eliminated_specs["separated"] += 1
            # return "flag_separated"
            return "true"
        elif ctx.OLD():
            if self.type_guided:
                self.is_in_old_logic_func = True
                res = self.visit(ctx.pred()[0])
                self.is_in_old_logic_func = False
                return res
            else:
                return "old(" + self.visit(ctx.pred()[0]) + ")"
        # elif pred.startswith(r"\valid_read"):
        elif ctx.VALIDREAD():
            if self.type_guided:
                if not ctx.location():
                    # '\\valid_read' '(' IDENT '+' '(' term '..' term ')' ')'
                    if self.is_in_logic_func:
                        res = ctx.IDENT().getText() + r"@." + r"len() >= "
                    else:
                        res = ctx.IDENT().getText() + r"@." + r"len() >= "
                        for item in self.cached_typed_items:
                            # if current acsl annotation is a function contract
                            if item[
                                "index"
                            ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                for param in item["items"]:
                                    if param["name"] == ctx.IDENT().getText().strip():
                                        if RustTypeAnalyzer.is_type_str_ref(
                                            param["type"]
                                        ):
                                            str_ident = self.visit(ctx.IDENT())
                                            res = f"""((forall|i: int| 0 <= i < {str_ident}@.len() - 1 ==> ({str_ident}@[(i) as int] != '\\0')) && {str_ident}@[{str_ident}@.len()-1]=='\\0')"""
                                            return res
                                        if RustTypeAnalyzer.is_type_slice(
                                            param["type"]
                                        ):
                                            res = (
                                                # ctx.IDENT().getText()
                                                self.visit(ctx.IDENT())
                                                + r"@."
                                                + r"len() >= "
                                            )
                                        else:
                                            if (
                                                self.eliminated_specs.get("validity")
                                                is None
                                            ):
                                                self.eliminated_specs["validity"] = 0
                                            self.eliminated_specs["validity"] += 1
                                            # return "flag_valid"
                                            return "true"
                            # if current acsl annotation is not a function contract
                            elif item[
                                "index"
                            ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                if item["item"] == ctx.IDENT().getText().strip():
                                    IDENT_type = item["type"]
                                    if RustTypeAnalyzer.is_type_str_ref(IDENT_type):
                                        str_ident = self.visit(ctx.IDENT())
                                        res = f"""((forall|i: int| 0 <= i < {str_ident}@.len() - 1 ==> ({str_ident}@[(i) as int] != '\\0')) && {str_ident}@[{str_ident}@.len()-1]=='\\0')"""
                                        return res
                                    if RustTypeAnalyzer.is_type_slice(IDENT_type):
                                        res = (
                                            self.visit(ctx.IDENT())
                                            + r"@."
                                            + r"len() >= "
                                            # ctx.IDENT().getText() + r"@." + r"len() >= "
                                        )
                                    else:
                                        if (
                                            self.eliminated_specs.get("validity")
                                            is None
                                        ):
                                            self.eliminated_specs["validity"] = 0
                                        self.eliminated_specs["validity"] += 1
                                        # return "flag_valid"
                                        return "true"
                    return res + self.visit(ctx.term()[1]) + " + 1"
                else:
                    # '\\valid_read' '(' location ')'
                    location = self.visit(ctx.location())
                    if self.is_in_logic_func:
                        # res = "(" + location + r")@." + r"len() >= " + r"1"
                        if self.eliminated_specs.get("validity") is None:
                            self.eliminated_specs["validity"] = 0
                        self.eliminated_specs["validity"] += 1
                        # return "flag_valid"
                        return "true"
                    else:
                        res = r"(" + location + r")@." + r"len() >= " + r"1"
                        non_typed_item_extracter = NonTypedItemExtractor(
                            lang_lib=self.lang_lib, logger=self.logger
                        )
                        non_typed_location = non_typed_item_extracter.visit(
                            ctx.location()
                        )
                        for item in self.cached_typed_items:
                            if item[
                                "index"
                            ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                for param in item["items"]:
                                    # as usual, location in the function contract is a formal parameter.
                                    if (
                                        param["name"]
                                        == ctx.location().getText().strip()
                                    ):
                                        location_type = param["type"]
                                        if RustTypeAnalyzer.is_type_str_ref(
                                            location_type
                                        ):
                                            return (
                                                r"("
                                                + location
                                                + r")@."
                                                + r"len() >= "
                                                + r"1 + 1"
                                            )
                                        if RustTypeAnalyzer.is_type_slice(
                                            location_type
                                        ):
                                            return (
                                                r"("
                                                + location
                                                + r")@."
                                                + r"len() >= "
                                                + r"1"
                                            )
                                        else:
                                            if (
                                                self.eliminated_specs.get("validity")
                                                is None
                                            ):
                                                self.eliminated_specs["validity"] = 0
                                            self.eliminated_specs["validity"] += 1
                                            # return "flag_valid"
                                            return "true"
                            elif item[
                                "index"
                            ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                if item["item"] == non_typed_location.strip():
                                    location_type = item["type"]
                                    if RustTypeAnalyzer.is_type_str_ref(location_type):
                                        return (
                                            r"("
                                            + location
                                            + r")@."
                                            + r"len() >= "
                                            + r"1 + 1"
                                        )
                                    if RustTypeAnalyzer.is_type_slice(location_type):
                                        return (
                                            r"("
                                            + location
                                            + r")@."
                                            + r"len() >= "
                                            + r"1"
                                        )
                                    else:
                                        if (
                                            self.eliminated_specs.get("validity")
                                            is None
                                        ):
                                            self.eliminated_specs["validity"] = 0
                                        self.eliminated_specs["validity"] += 1
                                        # return "flag_valid"
                                        return "true"
                    return res
            else:
                if not ctx.location():
                    if self.is_in_logic_func:
                        res = ctx.IDENT().getText() + r"@." + r"len() >= "
                    else:
                        res = ctx.IDENT().getText() + r"@." + r"len() >= "
                    return res + self.visit(ctx.term()[1]) + " + 1"
                else:
                    return "true"
        elif ctx.VALID():
            if self.type_guided:
                if not ctx.location():
                    # '\\valid' '(' IDENT '+' '(' term '..' term ')' ')'
                    # res = ctx.IDENT().getText() + r"." + r"len() >= "
                    res = None
                    if self.is_in_logic_func:
                        res = ctx.IDENT().getText() + r"@." + r"len() >= "
                    else:
                        res = self.visit(ctx.IDENT()) + r"@." + r"len() >= "
                        for item in self.cached_typed_items:
                            if item[
                                "index"
                            ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                for param in item["items"]:
                                    if param["name"] == ctx.IDENT().getText().strip():
                                        if RustTypeAnalyzer.is_type_str_ref(
                                            param["type"]
                                        ):
                                            str_ident = self.visit(ctx.IDENT())
                                            res = f"""((forall|i: int| 0 <= i < {str_ident}@.len() - 1 ==> ({str_ident}@[(i) as int] != '\\0')) && {str_ident}@[{str_ident}@.len()-1]=='\\0')"""
                                            return res
                                        if RustTypeAnalyzer.is_type_slice(
                                            param["type"]
                                        ):
                                            res = (
                                                self.visit(ctx.IDENT())
                                                + r"@."
                                                + r"len() >= "
                                            )
                                        else:
                                            if (
                                                self.eliminated_specs.get("validity")
                                                is None
                                            ):
                                                self.eliminated_specs["validity"] = 0
                                            self.eliminated_specs["validity"] += 1
                                            # return "flag_valid"
                                            return "true"
                            elif item[
                                "index"
                            ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                if item["item"] == ctx.IDENT().getText().strip():
                                    IDENT_type = item["type"]
                                    if RustTypeAnalyzer.is_type_str_ref(IDENT_type):
                                        str_ident = self.visit(ctx.IDENT())
                                        res = f"""((forall|i: int| 0 <= i < {str_ident}@.len() - 1 ==> ({str_ident}@[(i) as int] != '\\0')) && {str_ident}@[{str_ident}@.len()-1]=='\\0')"""
                                        return res
                                    if RustTypeAnalyzer.is_type_slice(IDENT_type):
                                        res = (
                                            self.visit(ctx.IDENT())
                                            + r"@."
                                            + r"len() >= "
                                        )
                                    else:
                                        if (
                                            self.eliminated_specs.get("validity")
                                            is None
                                        ):
                                            self.eliminated_specs["validity"] = 0
                                        self.eliminated_specs["validity"] += 1
                                        return "true"
                    return res + self.visit(ctx.term()[1]) + " + 1"
                else:
                    # '\\valid' '(' location ')'
                    location = self.visit(ctx.location())
                    # res = location + r"." + r"len() >= " + r"1"
                    res = None
                    if self.is_in_logic_func:
                        # res = "(" + location + r")@." + r"len() >= " + r"1"
                        if self.eliminated_specs.get("validity") is None:
                            self.eliminated_specs["validity"] = 0
                        self.eliminated_specs["validity"] += 1
                        # return "flag_valid"
                        return "true"
                    else:
                        res = "(" + location + r")@." + r"len() >= " + r"1"
                        non_typed_item_extracter = NonTypedItemExtractor(
                            lang_lib=self.lang_lib, logger=self.logger
                        )
                        non_typed_location = non_typed_item_extracter.visit(
                            ctx.location()
                        )
                        for item in self.cached_typed_items:
                            if item[
                                "index"
                            ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                for param in item["items"]:
                                    # as usual, location in the function contract is a formal parameter.
                                    if (
                                        param["name"]
                                        == ctx.location().getText().strip()
                                    ):
                                        location_type = param["type"]
                                        if RustTypeAnalyzer.is_type_str_ref(
                                            location_type
                                        ):
                                            return (
                                                r"("
                                                + location
                                                + r")@."
                                                + r"len() >= "
                                                + r"1 + 1"
                                            )
                                        if RustTypeAnalyzer.is_type_slice(
                                            location_type
                                        ):
                                            return (
                                                "("
                                                + location
                                                + r")@."
                                                + r"len() >= "
                                                + r"1"
                                            )
                                        else:
                                            if (
                                                self.eliminated_specs.get("validity")
                                                is None
                                            ):
                                                self.eliminated_specs["validity"] = 0
                                            self.eliminated_specs["validity"] += 1
                                            return "true"
                            elif item[
                                "index"
                            ] == self.cur_comment_id and not RustTypeAnalyzer.is_typed_items_in_contract(
                                item
                            ):
                                if item["item"] == non_typed_location.strip():
                                    location_type = item["type"]
                                    if RustTypeAnalyzer.is_type_str_ref(location_type):
                                        return (
                                            r"("
                                            + location
                                            + r")@."
                                            + r"len() >= "
                                            + r"1 + 1"
                                        )
                                    if RustTypeAnalyzer.is_type_slice(location_type):
                                        return (
                                            "("
                                            + location
                                            + r")@."
                                            + r"len() >= "
                                            + r"1"
                                        )
                                    else:
                                        if (
                                            self.eliminated_specs.get("validity")
                                            is None
                                        ):
                                            self.eliminated_specs["validity"] = 0
                                        self.eliminated_specs["validity"] += 1
                                        # return "flag_valid"
                                        return "true"
                    return res
            else:
                if not ctx.location():
                    res = None
                    if self.is_in_logic_func:
                        res = "old(" + ctx.IDENT().getText() + r")@." + r"len() >= "
                    else:
                        res = "old(" + self.visit(ctx.IDENT()) + r")@." + r"len() >= "
                    return res + self.visit(ctx.term()[1]) + " + 1"
                else:
                    return "true"
        elif ctx.FORALL() or ctx.EXISTS():
            # ('\\forall' | '\\exists') binder (',' binder)* ';' pred
            in_sink_binders = Taint2Sink().get_in_sink_binders(
                self.logic_func_slice_params, ctx
            )
            pred = self.visitChildren(ctx).strip()
            res = pred[0:6]
            vars = str()
            for binder in ctx.binder():
                vars += (
                    self.visitBinder_with_type_change(binder, in_sink_binders) + ", "
                )
            vars = vars.strip()[:-1]
            res += r"|" + vars + r"|"
            res += " "
            for p in ctx.pred():
                res += self.visitPred(p)
            return res
        else:
            # return "((" + self.visitChildren(ctx) + ") as int != 0)"
            return self.visitChildren(ctx)

    def visitBinder_with_type_change(self, ctx, in_sink_binders):
        if ctx.term()[0].getText() in in_sink_binders:
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": &[i32], "
            vars = vars.strip()[:-1]
            return vars
        else:
            return self.visitBinder(ctx)

    def visitBinder(self, ctx):
        """quantifier-qualified variable in predicate, e.g. forall, exists"""
        if ctx.logicAtomicType().getText() == "integer":
            # ident_num = len(ctx.IDENT()) if ctx.IDENT() else 0
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": int, "
            vars = vars.strip()[:-1]
            return vars
        elif ctx.logicAtomicType().getText() == "int":
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": i32, "
            vars = vars.strip()[:-1]
            return vars
        elif (
            ctx.logicAtomicType().getText() == "size_t"
            or ctx.logicAtomicType().getText() == "unsigned"
        ):
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": u32, "
            vars = vars.strip()[:-1]
            return vars
        elif ctx.logicAtomicType().getText() == "int*":
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": &i32, "
            vars = vars.strip()[:-1]
            return vars
        elif ctx.logicAtomicType().getText() == "boolean":
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": bool, "
            vars = vars.strip()[:-1]
            return vars
        elif ctx.logicAtomicType().getText() == "char*":
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": &str, "
            vars = vars.strip()[:-1]
            return vars
        elif ctx.logicAtomicType().getText() == "char":
            ident_num = len(ctx.term()) if ctx.term() else 0
            vars = str()
            for i in range(ident_num):
                vars += ctx.term()[i].getText() + r": char, "
            vars = vars.strip()[:-1]
            return vars
        else:
            error_msg = f"Verus doesn't support **real** type:\n{ctx.getText()}"
            self.logger_ctx_debug_info(ctx, error_msg=error_msg)
            self.error_type = TransformError.UnsupportedType
            self.return_code = -1
            raise ExitEarly(
                f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
            )

    def visitLogicAtomicType(self, ctx):
        if ctx.getText() == "int*":
            return "&i32"
        elif ctx.getText() == "char*":
            return "&str"
        else:
            return self.visitChildren(ctx)

    def visitLoopInvariant(self, ctx):
        return self.visit(ctx.pred())

    def visitLoopAssigns(self, ctx):
        if self.eliminated_specs.get("assigns") is None:
            self.eliminated_specs["assigns"] = 0
        self.eliminated_specs["assigns"] += 1
        # return "flag_assigns"
        return ""

    def visitLoopVariant(self, ctx):
        res = ""
        for child in ctx.children:
            if self.visit(child) == "loop":
                res += "decreases"
            elif self.visit(child) == "variant":
                res += " "
            elif self.visit(child) == ";":
                res += ","
            else:
                res += self.visit(child)
        return res

    def visitDecreasesClause(self, ctx):
        res = ""
        for child in ctx.children:
            if self.visit(child) == "decreases":
                res += "decreases "
            elif self.visit(child) == ";":
                res += ","
            else:
                res += self.visit(child)
        return res

    def visitTerminatesClause(self, ctx):
        # terminatesClause:  'terminates' pred  ';';
        error_msg = (
            f'"{ctx.getText()}" is a terminates-clause which cannnot be transformed.'
        )
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.TerminatesClause
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def visitNamedBehavior(self, ctx):
        """
        namedBehavior: 'behavior' IDENT ':' behaviorBody;
        behaviorBody -> pred ==> pred
        """
        return self.visit(ctx.behaviorBody())

    def visitBehaviorBody(self, ctx):
        """
        behaviorBody: assumesClause* requiresClause* simpleClause*;
        assume_pred && require_pred ==> ensure_pred
        Caution: should be after `ensuresClause`! Make sure `assume_pred && require_pred ==> ensure_pred` in ensure block!
        """
        is_first = True
        precond = ""
        for clause in ctx.assumesClause():
            if self.visitAssumesClause(clause).strip() != "":
                if is_first:
                    is_first = False
                    if self.type_guided:
                        self.is_in_old_logic_func = True
                        precond += "(" + self.visitAssumesClause(clause) + ")"
                        self.is_in_old_logic_func = False
                    else:
                        precond += "(" + self.visitAssumesClause(clause) + ")"
                else:
                    if self.type_guided:
                        self.is_in_old_logic_func = True
                        precond += "&&" + "(" + self.visitAssumesClause(clause) + ")"
                        self.is_in_old_logic_func = False
                    else:
                        precond += "&&" + "(" + self.visitAssumesClause(clause) + ")"
        for clause in ctx.requiresClause():
            if self.visitRequiresClause(clause).strip() != "":
                if is_first:
                    is_first = False
                    precond += "(" + self.visitRequiresClause(clause) + ")"
                else:
                    precond += "&&" + "(" + self.visitRequiresClause(clause) + ")"
        is_first = True
        post_cond = ""
        for clause in ctx.simpleClause():
            if clause.ensuresClause():
                if is_first:
                    post_cond += "(" + self.visit(clause) + ")"
                    is_first = False
                else:
                    post_cond += "&&" + "(" + self.visit(clause) + ")"
        if precond == "":
            precond = "true"
        if post_cond != "":
            return precond + " ==> " + post_cond
        else:
            return precond + " ==> true"

    def visitCompletenessClause(self, ctx):
        """
        completenessClause:
            'complete behaviors' (IDENT (',' IDENT)*)? ';'
            | 'disjoint behaviors' (IDENT (',' IDENT)*)? ';';
        Ignore this clause.
        """
        return ""

    def visitAssumesClause(self, ctx):
        # assumesClause: 'assumes' pred ';';
        return self.visit(ctx.pred())

    def visitCExternalDeclaration(self, ctx):
        res = ""
        for logicdef in ctx.logicDef():
            res += self.visitLogicDef(logicdef) + "\n"
        return res

    def visitLogicDef(self, ctx):
        if ctx.logicConstDef():
            return self.visitLogicConstDef(ctx.logicConstDef())
        elif ctx.logicFunctionDef():
            return self.visitLogicFunctionDef(ctx.logicFunctionDef())
        elif ctx.logicPredicateDef():
            return self.visitLogicPredicateDef(ctx.logicPredicateDef())
        elif ctx.lemmaDef():
            return self.visitLemmaDef(ctx.lemmaDef())
        elif ctx.inductiveDef():
            return self.visitInductiveDef(ctx.inductiveDef())
        elif ctx.axiomaticDecl():
            return self.visitAxiomaticDecl(ctx.axiomaticDecl())
        else:
            return ""

    def visitLogicConstDef(self, ctx):
        return

    def visitAxiomaticDecl(self, ctx):
        # axiomaticDecl: 'axiomatic' IDENT '{' logicDecl* '}';
        res = ""
        if ctx.logicDecl():
            for logicdecl in ctx.logicDecl():
                res += self.visitLogicDecl(logicdecl) + "\n"
            return res
        else:
            return res

        error_msg = f"The tool doesn't support transforming the **axiomaticDecl** in ACSL:\n{ctx.getText()}"
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.AxiomaticDecl
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def substitue_types_in_formal_params(self, input_str, id_list):
        """
        Replace `&i32` with `&[i32]`
        """
        params = [p.strip() for p in input_str.split(",") if p.strip()]

        new_params = []
        for idx, param in enumerate(params):
            if ":" not in param:
                new_params.append(param)
                continue
            if idx in id_list:
                name, _ = param.split(":", 1)
                new_params.append(f"{name.strip()}: &[i32]")
            else:
                new_params.append(param)

        new_params_str = ", ".join(new_params)
        return new_params_str

    def visitLogicFunctionDecl(self, ctx):
        self.is_in_logic_func = True
        if ctx.parameters():
            self.cur_logic_func_param_names = (
                self.extract_params_names_in_formal_params(self.visit(ctx.parameters()))
            )
        func_name = ctx.polyId().id_().IDENT().getText()

        is_int_slice_type_param_ids = []
        if self.type_guided:
            # Currently, only pay attention to int*!
            int_pointer_type_params = []
            for param_id, param in enumerate(ctx.parameters().parameter()):
                # self.logger.error(f"param_id:{param_id}\bparam:{param.getText()}")
                if isinstance(param, ACSLParser.ParameterContext):
                    if param.MUL() or param.typeExpr().getText().strip() == "int*":
                        int_pointer_type_params.append(
                            (param_id, self.visit(param.IDENT()))
                        )
            for param_id, _ in int_pointer_type_params:
                judge_result = RustTypeAnalyzer.is_uninterp_spec_fn_param_slice_type(
                    func_name, param_id, **self.type_guidance_args
                )
                if judge_result:
                    is_int_slice_type_param_ids.append(param_id)

        param_types = []
        for param in ctx.parameters().children:
            if isinstance(param, ACSLParser.ParameterContext):
                if param.MUL():
                    # ignore pointer type
                    param_types.append(None)
                else:
                    type_str = param.typeExpr().getText()
                    if "*" in type_str:
                        param_types.append(None)
                    else:
                        param_types.append(self.visit(param.typeExpr()))
        self.function_table[func_name] = ACSLFunctionSignature(param_types)

        spec_func_name = self.visit(ctx.polyId())
        formal_params = self.visit(ctx.parameters())
        formal_params = self.substitue_types_in_formal_params(
            formal_params, is_int_slice_type_param_ids
        )

        if ctx.parameters():
            param_types = self.extract_types_in_formal_params(formal_params)
            # raise ValueError(f"param_types: {param_types}")
            for id, t in enumerate(param_types):
                # id start from 0
                if t.strip() == "&[i32]":
                    if self.logic_func_slice_params.get(spec_func_name) is None:
                        self.logic_func_slice_params[spec_func_name] = []
                    self.logic_func_slice_params[spec_func_name].append(id)

        res = (
            "pub uninterp spec fn "
            + self.visit(ctx.polyId())
            + formal_params
            + " -> "
            + self.visit(ctx.typeExpr())
            + ";"
        )
        self.is_in_logic_func = False
        self.cur_logic_func_param_names = []
        return res

    def visitLogicPredicateDecl(self, ctx):
        self.is_in_logic_func = True
        if ctx.parameters():
            self.cur_logic_func_param_names = (
                self.extract_params_names_in_formal_params(self.visit(ctx.parameters()))
            )
        func_name = ctx.polyId().id_().IDENT().getText()

        is_int_slice_type_param_ids = []
        if self.type_guided:
            # Currently, only pay attention to int*!
            int_pointer_type_params = []
            for param_id, param in enumerate(ctx.parameters().parameter()):
                # self.logger.error(f"param_id:{param_id}\bparam:{param.getText()}")
                if isinstance(param, ACSLParser.ParameterContext):
                    if param.MUL() or param.typeExpr().getText().strip() == "int*":
                        int_pointer_type_params.append(
                            (param_id, self.visit(param.IDENT()))
                        )
            for param_id, _ in int_pointer_type_params:
                judge_result = RustTypeAnalyzer.is_uninterp_spec_fn_param_slice_type(
                    func_name, param_id, **self.type_guidance_args
                )
                if judge_result:
                    is_int_slice_type_param_ids.append(param_id)

        param_types = []
        for param in ctx.parameters().children:
            if isinstance(param, ACSLParser.ParameterContext):
                if param.MUL():
                    # ignore pointer type
                    param_types.append(None)
                else:
                    type_str = param.typeExpr().getText()
                    if "*" in type_str:
                        param_types.append(None)
                    else:
                        param_types.append(self.visit(param.typeExpr()))
        self.function_table[func_name] = ACSLFunctionSignature(param_types)

        spec_func_name = self.visit(ctx.polyId())
        formal_params = self.visit(ctx.parameters())
        formal_params = self.substitue_types_in_formal_params(
            formal_params, is_int_slice_type_param_ids
        )

        if ctx.parameters():
            param_types = self.extract_types_in_formal_params(formal_params)
            # raise ValueError(f"param_types: {param_types}")
            for id, t in enumerate(param_types):
                # id start from 0
                if t.strip() == "&[i32]":
                    if self.logic_func_slice_params.get(spec_func_name) is None:
                        self.logic_func_slice_params[spec_func_name] = []
                    self.logic_func_slice_params[spec_func_name].append(id)

        res = (
            "pub uninterp spec fn "
            + self.visit(ctx.polyId())
            + formal_params
            + " -> bool;"
        )
        self.is_in_logic_func = False
        self.cur_logic_func_param_names = []
        return res

    def visitAxiomDef(self, ctx):
        self.is_in_logic_func = True
        # broadcast lemmas
        self.broadcast_inductive_lemmas.append(self.visit(ctx.polyId()))
        proof_func = "pub broadcast proof fn" + " " + self.visit(ctx.polyId()) + "()"
        contract = "ensures\n\t" + self.visit(ctx.pred())
        res = "#[verifier::external_body]\n" + proof_func + "\n" + contract + "\n{\n}\n"
        self.is_in_logic_func = False
        return res

    def visitLogicDecl(self, ctx):
        if ctx.logicDef():
            return self.visit(ctx.logicDef())
        elif ctx.logicPredicateDecl():
            return self.visitLogicPredicateDecl(ctx.logicPredicateDecl())
        elif ctx.logicFunctionDecl():
            return self.visitLogicFunctionDecl(ctx.logicFunctionDecl())
        elif ctx.axiomDef():
            return self.visitAxiomDef(ctx.axiomDef())
        else:
            raise ValueError(
                f"SpecTransformer can't transform this logic declaration in axiomatic block:\n{ctx.getText()}"
            )
        return ""

    def visitReadsClause(self, ctx):
        # readsClause: 'reads' locations;
        error_msg = f"The tool doesn't support transforming the **reads-clause** in ACSL:\n{ctx.getText()}"
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.ReadsClause
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def visitLogicPredicateDef(self, ctx):
        self.is_in_logic_func = True
        if ctx.parameters():
            self.cur_logic_func_param_names = (
                self.extract_params_names_in_formal_params(self.visit(ctx.parameters()))
            )
        self.slicedetector.cache(
            self.logic_func_slice_params, self.cur_logic_func_param_names
        )
        self.slicedetector.visit(ctx.pred())

        func_name = ctx.polyId().id_().IDENT().getText()
        param_types = []
        if ctx.parameters():
            for param in ctx.parameters().children:
                if isinstance(param, ACSLParser.ParameterContext):
                    if param.MUL():
                        # ignore pointer type
                        param_types.append(None)
                    else:
                        type_str = param.typeExpr().getText()
                        if "*" in type_str:
                            param_types.append(None)
                        else:
                            param_types.append(self.visit(param.typeExpr()))
            self.function_table[func_name] = ACSLFunctionSignature(param_types)

        res = "pub open spec fn "
        spec_func_name = self.visit(ctx.polyId())
        res += spec_func_name
        if ctx.parameters():
            formal_params = self.visit(ctx.parameters())
            res += formal_params
            param_types = self.extract_types_in_formal_params(formal_params)

            for id, t in enumerate(param_types):
                # id start from 0
                if t.strip() == "&[i32]":
                    if self.logic_func_slice_params.get(spec_func_name) is None:
                        self.logic_func_slice_params[spec_func_name] = []
                    self.logic_func_slice_params[spec_func_name].append(id)
        else:
            res += "()"
        res += " -> bool {"
        res += self.visit(ctx.pred())
        res += "\n}"
        self.is_in_logic_func = False
        self.slicedetector.clean()
        self.cur_logic_func_param_names = []
        return res

    def getParameterNameList(self, ctx):
        # get the parameter names from inductiveDef parameters
        param_names = []
        for param in ctx.children:
            if isinstance(param, ACSLParser.ParameterContext):
                param_names.append(self.visit(param.IDENT()))
        return param_names

    def getBinderNameList(self, binder):
        # get the binder names from inductiveDef indcase binder
        name_list = []
        id_num = len(binder.term()) if binder.term() else 0
        for i in range(id_num):
            name_list.append(binder.term()[i].getText().strip())
        return name_list

    def getRecursiveCallTerm(self, ctx, function_name):
        if isinstance(ctx, ACSLParser.TermContext):
            if ctx.polyId():
                if self.visit(ctx.polyId()).strip() == function_name:
                    return ctx.term()
            else:
                for term in ctx.term():
                    res = self.getRecursiveCallTerm(term, function_name)
                    if res is not None:
                        return res
        elif isinstance(ctx, ACSLParser.PredContext):
            for child in ctx.children:
                if isinstance(child, ACSLParser.TermContext) or isinstance(
                    child, ACSLParser.PredContext
                ):
                    res = self.getRecursiveCallTerm(child, function_name)
                    if res is not None:
                        return res
        else:
            return None
        return None

    def getFixedParamValue(self, ctx, fixed_param_id, function_name):
        param_terms = self.getRecursiveCallTerm(ctx, function_name)
        if param_terms is not None:
            for param_id, param in enumerate(param_terms):
                if param_id == fixed_param_id:
                    return self.visit(param)
        else:
            raise ValueError(
                f"Cannot find the recursive call of {function_name} in {ctx.getText()}"
            )

    def getUnfixedParamId(self, ctx, unfixed_param_binder_name, function_name):
        param_terms = self.getRecursiveCallTerm(ctx, function_name)
        unfixed_id_list = []
        if param_terms is not None:
            for param_id, param in enumerate(param_terms):
                if unfixed_param_binder_name.strip() in self.visit(param).strip():
                    # The parameter expression where binder_variable occurs
                    unfixed_id_list.append(param_id)
            return unfixed_id_list
        else:
            raise ValueError(
                f"Cannot find the recursive call of {function_name} in {ctx.getText()}"
            )

    def visitInductiveDef(self, ctx):
        """Be refined via type guidance"""
        func_name = ctx.polyId().id_().IDENT().getText()

        is_int_slice_type_param_ids = []
        if self.type_guided:
            # Currently, only pay attention to int*!
            int_pointer_type_params = []
            for param_id, param in enumerate(ctx.parameters().parameter()):
                # self.logger.error(f"param_id:{param_id}\bparam:{param.getText()}")
                if isinstance(param, ACSLParser.ParameterContext):
                    if param.MUL() or param.typeExpr().getText().strip() == "int*":
                        int_pointer_type_params.append(
                            (param_id, self.visit(param.IDENT()))
                        )
            for param_id, _ in int_pointer_type_params:
                judge_result = RustTypeAnalyzer.is_uninterp_spec_fn_param_slice_type(
                    func_name, param_id, **self.type_guidance_args
                )
                if judge_result:
                    is_int_slice_type_param_ids.append(param_id)

        param_types = []
        for param in ctx.parameters().children:
            if isinstance(param, ACSLParser.ParameterContext):
                if param.MUL():
                    # ignore pointer type
                    param_types.append(None)
                else:
                    type_str = param.typeExpr().getText()
                    if "*" in type_str:
                        param_types.append(None)
                    else:
                        param_types.append(self.visit(param.typeExpr()))
        self.function_table[func_name] = ACSLFunctionSignature(param_types)

        spec_func_name = self.visit(ctx.polyId())
        formal_params = self.visit(ctx.parameters())
        formal_params = self.substitue_types_in_formal_params(
            formal_params, is_int_slice_type_param_ids
        )

        if ctx.parameters():
            param_types = self.extract_types_in_formal_params(formal_params)
            # raise ValueError(f"param_types: {param_types}")
            for id, t in enumerate(param_types):
                # id start from 0
                if t.strip() == "&[i32]":
                    if self.logic_func_slice_params.get(spec_func_name) is None:
                        self.logic_func_slice_params[spec_func_name] = []
                    self.logic_func_slice_params[spec_func_name].append(id)

        res = "pub uninterp spec fn "
        # spec_func_name = self.visit(ctx.polyId())
        res += spec_func_name
        if ctx.parameters():
            # formal_params = self.visit(ctx.parameters())
            res += formal_params
        else:
            res += "()"
        res += " -> bool;\n"

        proof_func_name = spec_func_name + "_inductive"
        self.broadcast_inductive_lemmas.append(proof_func_name)
        res += (
            "\n#[verifier::external_body]\npub broadcast proof fn "
            + proof_func_name
            + "()\n\tensures\n\t\t"
        )

        for case in ctx.indcase():
            res += self.visit(case.pred()) + ",\n"
        res += "{}"
        return res

        error_msg = f"The tool doesn't support transforming the **inductiveDef** in ACSL:\n{ctx.getText()}"
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.InductiveDef
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def visitLemmaDef(self, ctx):
        self.is_in_logic_func = True
        # broadcast lemmas
        self.broadcast_inductive_lemmas.append(self.visit(ctx.polyId()))
        if ctx.clauseKind():
            if ctx.clauseKind().ADMIT():
                proof_func = (
                    "pub broadcast proof fn" + " " + self.visit(ctx.polyId()) + "()"
                )
                contract = "ensures\n\t" + self.visit(ctx.pred())
                return (
                    "#[verifier::external_body]\n"
                    + proof_func
                    + "\n"
                    + contract
                    + "\n{\n}\n"
                )

        proof_func = "pub broadcast proof fn" + " " + self.visit(ctx.polyId()) + "()"
        contract = "ensures\n\t" + self.visit(ctx.pred())
        res = proof_func + "\n" + contract + "\n{\n}\n"
        self.is_in_logic_func = False
        return res

    def visitLogicFunctionDef(self, ctx):

        self.is_in_logic_func = True

        if ctx.parameters():
            self.cur_logic_func_param_names = (
                self.extract_params_names_in_formal_params(self.visit(ctx.parameters()))
            )
        self.slicedetector.cache(
            self.logic_func_slice_params, self.cur_logic_func_param_names
        )
        self.slicedetector.visit(ctx.term())

        func_name = ctx.polyId().id_().IDENT().getText()
        param_types = []
        for param in ctx.parameters().children:
            if isinstance(param, ACSLParser.ParameterContext):
                if param.MUL():
                    # ignore pointer type
                    param_types.append(None)
                else:
                    type_str = param.typeExpr().getText()
                    if "*" in type_str:
                        param_types.append(None)
                    else:
                        param_types.append(self.visit(param.typeExpr()))
        self.function_table[func_name] = ACSLFunctionSignature(param_types)

        spec_func_name = self.visit(ctx.polyId())
        if ctx.parameters():
            formal_params = self.visit(ctx.parameters())
            param_types = self.extract_types_in_formal_params(formal_params)
            # raise ValueError(f"param_types: {param_types}")
            for id, t in enumerate(param_types):
                # id start from 0
                if t.strip() == "&[i32]":
                    if self.logic_func_slice_params.get(spec_func_name) is None:
                        self.logic_func_slice_params[spec_func_name] = []
                    self.logic_func_slice_params[spec_func_name].append(id)

        res = (
            "pub open spec"
            + " fn "
            + self.visit(ctx.polyId())
            + self.visit(ctx.parameters())
            + " -> "
            + self.visit(ctx.typeExpr())
            + "{\n"
            + self.visit(ctx.term())
            + "\n}"
        )
        self.is_in_logic_func = False
        self.slicedetector.clean()
        self.cur_logic_func_param_names = []
        return res

    def visitTypeVar(self, ctx):
        """
        typeVar:
            logicAtomicType
            | 'struct' IDENT
            | logicAtomicType '[' ']';
        """
        type_ident = self.visitChildren(ctx)
        if type_ident == "integer":
            return "int"
        elif type_ident == "int":
            return "i32"
        elif type_ident == "size_t" or type_ident == "unsigned":
            return "u32"
        elif type_ident == "boolean":
            return "bool"
        elif type_ident == "real":
            error_msg = f"Verus doesn't support **real** type:\n{ctx.getText()}"
            self.logger_ctx_debug_info(ctx, error_msg=error_msg)
            self.error_type = TransformError.UnsupportedType
            self.return_code = -1
            raise ExitEarly(
                f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
            )
        elif type_ident == "&i32":
            return "&i32"
        elif type_ident == "char":
            return "char"
        elif type_ident == "&str":
            return "&str"
        else:
            self.logger.error(f"{ctx.getText()}\n")
            self.logger.error(f'SpecTransformer Error in "visitTypeVar" method!\n')
            # TODO
            sys.exit(1)

    def visitTypeExpr(self, ctx):
        return self.visitChildren(ctx)

    def visitPolyId(self, ctx):
        return self.visitChildren(ctx)

    def visitTypeVarBinders(self, ctx):
        return self.visitChildren(ctx)

    def visitParameters(self, ctx):
        return self.visitChildren(ctx)

    def visitParameter(self, ctx):
        """
        parameter:
            typeExpr IDENT
            |typeExpr '*' IDENT;
        """
        if ctx.MUL():
            return "*" + self.visit(ctx.IDENT()) + ": " + self.visit(ctx.typeExpr())
        else:
            if self.visit(ctx.typeExpr()) == "&i32":
                if self.visit(ctx.IDENT()) in self.slicedetector.sliceIdent:
                    return self.visit(ctx.IDENT()) + ": &[i32]"
            return self.visit(ctx.IDENT()) + ": " + self.visit(ctx.typeExpr())

    def visitGhostCode(self, ctx):
        """
        ghostCode:
            '/*@' 'ghost' .*? '*/'
            | '//@' 'ghost' .*? LINEEND;
        """
        # return ""
        error_msg = f"{ctx.getText()} is **ghostCode** which cannnot be transformed."
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.GhostCode
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def visitLabelBinders(self, ctx):
        error_msg = f"{ctx.getText()} uses **labels** which cannnot be transformed."
        self.logger_ctx_debug_info(ctx, error_msg=error_msg)
        self.error_type = TransformError.Labels
        self.return_code = -1
        raise ExitEarly(
            f'SpecTransformer can\'t transform ACSL in this file "{self.file_path}"'
        )

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitIDENT(self, ctx):
        for item in self.cached_typed_items:
            if item[
                "index"
            ] == self.cur_comment_id and RustTypeAnalyzer.is_typed_items_in_contract(
                item
            ):
                for param in item["items"]:
                    if param["name"] == ctx.getText().strip():
                        if RustTypeAnalyzer.is_type_mut(param["type"]):
                            return "old(" + ctx.getText().strip() + ")"
                        else:
                            return ctx.getText().strip()
        return ctx.getText().strip()

    def visitTerminal(self, node):
        term = node.getText()
        if term == r"/*@":
            return ""
        elif term == r"*/":
            return ""
        elif term == r"//@":
            return ""
        elif term == r"requires":
            return term + " "
        elif term == r"ensures":
            return term + " "
        elif term == r"\forall":
            return "forall"
        elif term == r"\exists":
            return "exists"
        elif term == r"\result":
            return "result"
        elif term == r"\false":
            return "false"
        elif term == r"\true":
            return "true"
        elif term == r"INT_MAX":
            return "i32::MAX"
        elif term == r"INT_MIN":
            return "i32::MIN"
        elif term == r"UINT_MAX":
            return "u32::MAX"
        elif term == r"UINT_MIN":
            return "u32::MIN"
        elif term == r"\old":
            return "old"
        elif term == r"strlen":
            return "strlen"
        elif term == r"\max":
            return "max"
        elif term == r"\min":
            return "min"
        else:
            token = node.getSymbol()
            token_type = token.type
            if token_type == ACSLLexer.IDENT and self.is_in_old_logic_func:
                return self.visitIDENT(node)
            return term


class SpecTransformer:

    def __init__(self, file_path, lang_lib, logger, transpiled_rust, type_guidance):
        self.lang_lib = lang_lib
        self.logger = logger
        self.transpiled_rust = transpiled_rust
        self.visitor = ACSL2Verus(
            file_path=file_path,
            lang_lib=lang_lib,
            logger=logger,
            type_guidance=type_guidance,
        )
        self.source_file_path = file_path

        self.acslrewriter = ACSLRewriter(logger=logger)
        self.error_type = None
        self.visitor.return_code = 0
        self.return_code = 0
        pass

    def get_eliminated_spec(self):
        res = self.visitor.get_eliminated_spec().copy()
        self.logger.error(
            f"C File Path:\n{self.source_file_path}\nEliminated Specs:\n{res}\n"
        )
        return res

    def transform(self, acsl_info, temp_dir):
        """transform ACSL to Verus"""
        contexts = acsl_info["context"]
        acsl_codes = acsl_info["annotation"]
        verus_codes = []

        type_analyzer = RustTypeAnalyzer(lang_lib=self.lang_lib)
        typed_items = type_analyzer.type_analysis(
            rust_file_path=self.transpiled_rust,
            acsl_info=acsl_info,
            target_project_dir=temp_dir,
        )
        type_guidance_args = {
            "rust_file_path": self.transpiled_rust,
            "acsl_info": acsl_info,
            "target_project_dir": temp_dir,
        }
        self.visitor.type_guidance_args = type_guidance_args
        self.visitor.updata_cached_typed_items(typed_items)
        for id, acsl_code in enumerate(acsl_codes):
            acsl_code = self.acslrewriter.rewrite(code=acsl_code)

            self.visitor.cur_comment_id = id

            input_stream = InputStream(acsl_code)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()
            try:
                verus_code = self.visitor.visit(tree)
            except ExitEarly as e:
                self.logger.error(
                    f"Failure during transforming **ACSL** specification to **Verus** specification:\n[ACSL]:\n{acsl_code}\n"
                )
                self.error_type = self.visitor.error_type
                self.return_code = -1
                return None

            self.logger.info(
                f"Transform **ACSL** specification to **Verus** specification:\n[ACSL]:\n{acsl_code}\n"
                + "-" * 80
                + "\n"
                + f"[Verus]:\n{verus_code}\n"
            )
            verus_codes.append(verus_code)
        return {"context": contexts, "annotation": verus_codes}


if __name__ == "__main__":
    pass
