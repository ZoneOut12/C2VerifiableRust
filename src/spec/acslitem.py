import sys, os, re
from antlr4 import InputStream, CommonTokenStream
from antlr4.ListTokenSource import ListTokenSource
from antlr4.Token import Token
from antlr4.error.ErrorListener import ErrorListener
from tree_sitter import Language, Parser
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor


class DerefErrorListener(ErrorListener):
    def __init__(self):
        self.has_error = False

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        self.has_error = True


class NonTypedItemExtractor(ACSLParserVisitor):
    def __init__(self, lang_lib, logger=None):
        super().__init__()
        self.lang_lib = lang_lib
        self.logger = logger
        LANGUAGE_LIB = self.lang_lib
        RUST_LANGUAGE = Language(LANGUAGE_LIB, "rust")
        self.rust_parser = Parser()
        self.rust_parser.set_language(RUST_LANGUAGE)
        self.items = set()
        self.dereference = 0

    def printlog(self, *args, sep=" ", end="\n"):
        msg = sep.join(str(arg) for arg in args) + end
        if self.logger:
            self.logger.info(msg)
        else:
            print(*args, sep=sep, end=end)

    def query_contract_position(self, context, rust_code):
        """Needed to audit!"""
        func_name = context["func_name"]
        byte_code = rust_code.encode("utf8")
        tree = self.rust_parser.parse(byte_code)
        root_node = tree.root_node

        def walk(node):
            if node.type == "function_item":
                ident = node.child_by_field_name("name")
                if ident:
                    if (
                        byte_code[ident.start_byte : ident.end_byte].decode()
                        == func_name
                    ):
                        return node.start_point

            for child in node.children:
                result = walk(child)
                if result:
                    return result
            return None

        return walk(root_node)

    def query_loop_position(self, context, rust_code):
        func_name = context["func_name"]
        loop_id = context["loop_id"]
        byte_code = rust_code.encode("utf8")
        tree = self.rust_parser.parse(byte_code)
        root_node = tree.root_node

        def find_function(node):
            if node.type == "function_item":
                ident = node.child_by_field_name("name")
                if ident:
                    if (
                        byte_code[ident.start_byte : ident.end_byte].decode()
                        == func_name
                    ):
                        return node
            for child in node.children:
                result = find_function(child)
                if result:
                    return result
            return None

        def find_loops(node):
            loops = []

            def visit(n):
                if n.type in {"loop_expression", "for_expression", "while_expression"}:
                    loops.append(n)
                for child in n.children:
                    visit(child)

            visit(node)
            return loops

        func_node = find_function(root_node)
        if not func_node:

            raise ValueError(f"Function '{func_name}' not found")
        body_node = func_node.child_by_field_name("body")
        if not body_node:
            raise ValueError("Function '{func_name}' has no body")

        loops = find_loops(body_node)
        if loop_id > len(loops):
            raise ValueError(
                f"Only found {len(loops)} loops, but requested index {loop_id}"
            )

        loop_node = loops[loop_id - 1]
        block = loop_node.child_by_field_name("body")
        if block and block.type == "block":
            return block.start_point  # (row, column)
        else:
            raise ValueError("Loop has no block body")

    def query_assert_position(self, context, rust_code):
        assert_id = context["assert_id"]
        byte_code = rust_code.encode("utf8")
        tree = self.rust_parser.parse(byte_code)
        root_node = tree.root_node

        def walk(node):
            if node.type == "line_comment":
                comment_text = node.text.decode("utf-8")
                match = re.match(r"//\s*verus_assert\((\d+)\)\s*;", comment_text)
                if match:
                    cur_comment_id = int(match.group(1))
                    if cur_comment_id == assert_id:
                        return node.start_point
            for child in node.children:
                result = walk(child)
                if result:
                    return result
            return None

        return walk(root_node)

    def query_position(self, context, rust_code):
        if context["func_name"] is not None:
            if context["loop_id"] == 0 and context["assert_id"] == 0:
                return self.query_contract_position(context, rust_code)
            elif context["loop_id"] > 0:
                return self.query_loop_position(context, rust_code)
            elif context["assert_id"] > 0:
                return self.query_assert_position(context, rust_code)
        return None

    def extract_non_typed_items(self, acsl_info, rust_file_path):
        """
        Param:
        acsl_info: acsl annotations and corresponding context
        rust_file_path: transpiled rust code
        """
        with open(rust_file_path, "r") as f:
            rust_code = f.read()
        contexts = acsl_info["context"]
        acsl_codes = acsl_info["annotation"]

        items_with_position = []

        for id, acsl_code in enumerate(acsl_codes):
            context = contexts[id]
            if context["func_name"] is None:
                continue
            elif context["loop_id"] == 0 and context["assert_id"] == 0:
                items_with_position.append(
                    {"index": id, "items": set(), "position": context["func_name"]}
                )
                continue
            try:
                position = self.query_position(context, rust_code)
            except Exception as e:
                if self.logger:
                    self.logger.error(
                        f"Error querying position for ACSL annotation {id}:\n{e}\n"
                    )
                position = None

            input_stream = InputStream(acsl_code)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()
            self.visit(tree)
            if position is not None:
                # index: the i-th acsl annotation(start from 0) , items: the items needed type inference, position: the position of the type inference point
                items_with_position.append(
                    {"index": id, "items": self.items.copy(), "position": position}
                )
            self.items.clear()

        return items_with_position

    def visitTerm(self, ctx):
        if ctx.ARROW():
            # term: term '->' IDENT
            return self.visit(ctx.term()[0]) + "." + self.visit(ctx.IDENT())
        elif ctx.MUL() and ctx.getChildCount() == 2:
            # term: '*' term
            if self.dereference > 0:
                self.dereference -= 1
                res = self.visit(ctx.term()[0])
                self.items.add(res)
                return res
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
                listener = DerefErrorListener()
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
        elif ctx.OLD():
            # term: '\\old' '(' term ')'
            return self.visit(ctx.term()[0])
        return self.visitChildren(ctx)

    def visitTset(self, ctx):
        if ctx.ARROW():
            # tset: tset '->' IDENT
            return self.visit(ctx.tset()[0]) + "." + self.visit(ctx.IDENT())
        elif ctx.MUL() and ctx.getChildCount() == 2:
            # tset: '*' tset
            if self.dereference > 0:
                self.dereference -= 1
                res = self.visit(ctx.tset()[0])
                self.items.add(res)
                return res
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
                listener = DerefErrorListener()
                acsl_parser.removeErrorListeners()
                acsl_parser.addErrorListener(listener)
                tree = acsl_parser.tset()
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
        return self.visitChildren(ctx)

    def visitPred(self, ctx):
        if ctx.OLD():
            # pred: '\\old' '(' pred ')'
            return self.visit(ctx.pred()[0])
        elif ctx.VALID() or ctx.VALIDREAD():
            if ctx.IDENT():
                self.items.add(self.visit(ctx.IDENT()))
            else:
                self.items.add(self.visit(ctx.location()))
        return self.visitChildren(ctx)

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitTerminal(self, node):
        return node.getText()


if __name__ == "__main__":
    pass
