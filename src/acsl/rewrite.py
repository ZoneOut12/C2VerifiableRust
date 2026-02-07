import sys, re, tempfile, os
from tree_sitter import Language, Parser
from antlr4 import InputStream, CommonTokenStream
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from src.utils.frama import Frama
from src.acsl.acsltree import ACSLStructuralTree


class TreeSitterPointerAnalyzer:
    """
    Analyze the usage semantics of pointer variables which occurred in the 'xxx.c'.
    (Context, Pointer variable) in which Context is denoted by funciton name.
    """

    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.current_function = ""
        pass

    def analyze_file(self, path):
        with open(path, "r", encoding="utf-8") as f:
            code = f.read()

        tree = self.parser.parse(bytes(code, "utf8"))
        root = tree.root_node

        pointers = set()
        arrays = set()

        self._walk(root, code, pointers, arrays)

        # return all the pointer variables and usage semantics(array or scalar)
        result = {}
        for p in pointers:
            result[p] = "array" if p in arrays else "scalar"
        return result

    def _walk(self, node, code, pointers, arrays):
        # enter the scope of new function
        if node.type == "function_definition":
            decl = node.child_by_field_name("declarator")
            func_name_node = decl.child_by_field_name("declarator") if decl else None
            if func_name_node and func_name_node.type == "identifier":
                self.current_function = func_name_node.text.decode("utf-8")

        # record variable declarationn：int *p;
        elif node.type == "pointer_declarator":
            ident = self._find_identifier(node)
            if ident:
                pointers.add((self.current_function, ident))

        # check `p[i]` usage（subscript_expression）
        elif node.type == "subscript_expression":
            var = self._get_identifier_name(node.child_by_field_name("argument"))
            if var:
                arrays.add((self.current_function, var))

        # check `*(p + i)` usage（unary_expression -> binary_expression）
        elif node.type == "unary_expression" and node.child_by_field_name("argument"):
            arg = node.child_by_field_name("argument")
            if arg.type == "binary_expression" and arg.child_count >= 2:
                left = self._get_identifier_name(arg.children[0])
                if left:
                    arrays.add((self.current_function, left))

        for child in node.children:
            self._walk(child, code, pointers, arrays)

    def _get_identifier_name(self, node):
        if node is None:
            return None
        if node.type == "identifier":
            return node.text.decode("utf-8")
        return None

    def _find_identifier(self, node):
        for child in node.children:
            if child.type == "identifier":
                return child.text.decode("utf-8")
        return None


class PointerMutationAnalyzer:
    """
    Analyze whether the Pointer Parameters of a function have been mutated in the funciton body.
    Current implementation is simple(e.g. intraprocedural analysis).
    Check Method:
        check whether Left-hand-side of the Assignment expression is the format of 'pointer_expression'(e.g. *p, *(p+i)) or 'subscript_expression'(e.g. p[i]).
    """

    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        pass

    def extract_mutated_pointers_with_context(self, file_path):
        code = None
        with open(file_path, "r") as f:
            code = f.read()
        tree = self.parser.parse(code.encode())
        code = code.encode()
        root = tree.root_node
        mutated = set()
        params = set()

        def is_pointer_parameter(param_node):

            if (
                param_node.child_by_field_name("declarator")
                and param_node.child_by_field_name("declarator").type
                == "pointer_declarator"
            ):
                return (
                    param_node.child_by_field_name("declarator")
                    .child_by_field_name("declarator")
                    .text.decode()
                )
            else:
                return None

        def collect_pointer_params(node):
            # enter the scope of new function
            if node.type == "function_definition":
                decl = node.child_by_field_name("declarator")
                func_name_node = (
                    decl.child_by_field_name("declarator") if decl else None
                )
                if func_name_node and func_name_node.type == "identifier":
                    current_func_name = func_name_node.text.decode("utf-8")

                if decl:
                    for child in decl.children:
                        if child.type == "parameter_list":
                            for param in child.children:
                                if param.type == "parameter_declaration":
                                    name = is_pointer_parameter(param)
                                    if name:
                                        params.add((current_func_name, name))

            for child in node.children:
                collect_pointer_params(child)

        def find_mutations(node, func_context):
            if node.type == "function_definition":
                decl = node.child_by_field_name("declarator")
                func_name_node = (
                    decl.child_by_field_name("declarator") if decl else None
                )
                if func_name_node and func_name_node.type == "identifier":
                    func_context = func_name_node.text.decode("utf-8")
                for child in node.children:
                    find_mutations(node=child, func_context=func_context)
                return

            if node.type == "assignment_expression":
                lhs = node.children[0]
                if self.is_pointer_write(lhs, params, func_context):
                    var_name = self.extract_identifier(lhs)
                    if var_name:
                        mutated.add((func_context, var_name))
            for child in node.children:
                find_mutations(child, func_context)

        collect_pointer_params(root)
        find_mutations(root, None)
        return mutated

    def is_pointer_write(self, node, params, func_context):
        """
        Checks if the LHS node is *p or p[i], where p is a parameter.
        """
        if node.type == "pointer_expression":
            id_node = self.find_identifier(node)
            if id_node:
                name = id_node.text.decode()
                return (func_context, name) in params
        if node.type == "subscript_expression":
            id_node = self.find_identifier(node)
            if id_node:
                name = id_node.text.decode()
                return (func_context, name) in params
        return False

    def find_identifier(self, node):
        """
        Recursively find an identifier under this node.
        """
        if node.type == "identifier":
            return node
        for child in node.children:
            found = self.find_identifier(child)
            if found:
                return found
        return None

    def extract_identifier(self, node):
        id_node = self.find_identifier(node)
        return id_node.text.decode() if id_node else None


class Valid2ValidRead:
    def __init__(self, lang_lib):
        self.verifier = Frama()
        self.treebuilder = ACSLStructuralTree(lang_lib=lang_lib)
        self.pattern = re.compile(r"\\valid\(")
        pass

    def split_code_by_acsl_annotations(self, code):
        """
        Split C code based on ACSL annotations.
        Return a list consisting of code snippets.
        The odd index if the return list is related to ACSL annotations.
        """
        pattern = re.compile(r"(/\*@[\s\S]*?\*/|//@.*)")

        fragments = []
        acsl_indices = []
        last_end = 0

        for match in pattern.finditer(code):
            start, end = match.span()
            if start > last_end:
                fragments.append(code[last_end:start])
            acsl_indices.append(len(fragments))
            fragments.append(code[start:end])
            last_end = end

        if last_end < len(code):
            fragments.append(code[last_end:])

        return fragments, acsl_indices

    def replace_and_join(self, lst, index, new_element):
        return "".join(new_element if i == index else s for i, s in enumerate(lst))

    def rewrite(self, file_path):
        code = ""
        with open(file_path, "r") as f:
            code = f.read()

        self.treebuilder.build(code)
        order = self.treebuilder.reverse_post_order_traversal()
        snippets_list, acsl_indices = self.split_code_by_acsl_annotations(code)

        modified = False
        for ord in order:
            index = acsl_indices[ord - 1]
            acsl = snippets_list[index]

            matches = list(self.pattern.finditer(acsl))
            if not matches:
                continue

            offset = 0

            for match in matches:
                start, end = match.start() + offset, match.end() + offset

                new_acsl = acsl[:start] + r"\valid_read(" + acsl[end:]
                new_code = self.replace_and_join(snippets_list, index, new_acsl)

                with tempfile.NamedTemporaryFile(
                    "w", delete=False, suffix=".c"
                ) as tmp_file:
                    tmp_file.write(new_code)
                    tmp_path = tmp_file.name

                try:
                    if self.verifier.verify(tmp_path):
                        acsl = new_acsl
                        offset += len(r"\valid_read(") - len(r"\valid(")
                        modified = True
                finally:
                    os.remove(tmp_path)

            snippets_list[index] = acsl

        if modified:
            return True

        return False

    def remove_non_acsl_comments(self, code):
        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)
        return code


class ValidRewriter(ACSLParserVisitor):
    """
    Replace some unnecessary `\valid(IDENT)` or `\valid_read(IDENT)` with `\true`, when IDENT is used to point to a scalar.
    """

    def __init__(self, lang_lib, logger=None):
        super().__init__()
        self.analyzer = TreeSitterPointerAnalyzer(lang_lib)
        self.analysis_result = {}
        self.mutParamAnalyzer = PointerMutationAnalyzer(lang_lib)
        self.mutParams = {}
        self.func_name = ""
        self.logger = logger

    def rewrite(self, code, func_name, file_path):
        """
        code: ACSL annotation snippet
        func_name: 'func_name' in the Context of ACSL annotation snippet
        file_path: original C file path
        """
        if func_name is None:
            return code

        input_stream = InputStream(code)
        lexer = ACSLLexer(input_stream)
        token_stream = CommonTokenStream(lexer)
        parser = ACSLParser(token_stream)
        tree = parser.acsl()
        self.analysis_result = self.analyzer.analyze_file(file_path)
        self.mutParams = self.mutParamAnalyzer.extract_mutated_pointers_with_context(
            file_path
        )
        self.func_name = func_name
        return self.visit(tree)

    def is_valid_IDENT(self, text):
        return re.fullmatch(r"[a-zA-Z][a-zA-Z0-9_]*", text) is not None

    def visitPred(self, ctx):
        if ctx.VALID() and ctx.location():
            text = ctx.location().getText().strip()
            is_IDENT = self.is_valid_IDENT(text=text)
            if is_IDENT:
                if self.analysis_result.get((self.func_name, text), None) == "scalar":
                    return "\\true"
            return super().visitPred(ctx)

        elif ctx.VALID() and ctx.IDENT():
            # if `p` of `\valid(p + ( range ))` is not mutated, change `\valid(p + ( range ))` into `\valid_read(p + ( range ))`
            # ignored, there is nothing done.
            text = ctx.IDENT().getText().strip()
            return super().visitPred(ctx)

        elif ctx.VALIDREAD() and ctx.location():
            text = ctx.location().getText().strip()
            is_IDENT = self.is_valid_IDENT(text=text)
            if is_IDENT:
                if self.analysis_result.get((self.func_name, text), None) == "scalar":
                    return "\\true"
            return super().visitPred(ctx)

        else:
            return super().visitPred(ctx)

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitTerminal(self, ctx):
        return " " + ctx.getText() + " "


class OldRewriter(ACSLParserVisitor):
    def __init__(self, logger):
        super().__init__()
        self.logger = logger
        self.is_old = False
        self.is_old_var = True

    def rewrite(self, code):
        input_stream = InputStream(code)
        lexer = ACSLLexer(input_stream)
        token_stream = CommonTokenStream(lexer)
        parser = ACSLParser(token_stream)
        tree = parser.acsl()
        return self.visit(tree)

    def visitTerm(self, ctx):
        if ctx.OLD():
            self.is_old = True
            term = ctx.term()[0]
            res = self.visitTerm(term)
            self.is_old = False
            return res
        elif ctx.getChildCount() == 4 and ctx.getChild(1).getText() == "[":
            # match grammar rule `term: term '[' term ']'`.
            # the first term is the array name, the second term is the index.
            # the index should not be wrapped in `\old()``, but the array name should be wrapped in `\old()`.
            res = self.visitTerm(ctx.term()[0])
            self.is_old_var = False
            res += "[" + self.visitTerm(ctx.term()[1]) + "]"
            self.is_old_var = True
            return res
        else:
            return self.visitChildren(ctx)

    def visitIDENT(self, ctx):
        if self.is_old and self.is_old_var:
            return "\\old(" + ctx.getText() + ")"
        else:
            return ctx.getText()

    def visitPred(self, ctx):
        if ctx.OLD():
            self.is_old = True
            pred = ctx.pred()
            res = self.visitPred(pred)
            self.is_old = False
            return res
        else:
            return self.visitChildren(ctx)

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitTerminal(self, ctx):
        token = ctx.getSymbol()
        token_type = token.type
        if token_type == ACSLLexer.IDENT:
            return " " + self.visitIDENT(ctx) + " "
        return " " + ctx.getText() + " "


class ACSLRewriter(ACSLParserVisitor):
    def __init__(self, logger):
        super().__init__()
        self.logger = logger

    def rewrite(self, code):
        # rewrite function call `ident(params)` to `(ident(params))`
        input_stream = InputStream(code)
        lexer = ACSLLexer(input_stream)
        token_stream = CommonTokenStream(lexer)
        parser = ACSLParser(token_stream)
        tree = parser.acsl()
        return self.visit(tree)

    def visitTerm(self, ctx):
        if ctx.polyId():
            return "(" + self.visitChildren(ctx) + ")"
        return super().visitTerm(ctx)

    def visitChildren(self, ctx):
        res = ""
        for child in ctx.children:
            res += self.visit(child)
        return res

    def visitTerminal(self, ctx):
        return " " + ctx.getText() + " "


if __name__ == "__main__":
    pass
