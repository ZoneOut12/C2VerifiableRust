import os, tempfile
from src.utils.tree_sitter_parse import TreeSitterParser, TypeClassifier, TypeKind
from src.analysis.lsp import RustAnalyzerClient
from src.spec.acslitem import NonTypedItemExtractor
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from antlr4 import InputStream, CommonTokenStream
from src.utils.logger import DummyLogger


class FnNameMeet(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return f"{self.message}"


class FnCallMeet(Exception):
    def __init__(self, message, param_list=None):
        self.message = message
        self.param_list = param_list or []

    def __str__(self):
        return f"{self.message}"


class SpecFncCallPositionSearcher(ACSLParserVisitor):
    def __init__(self, lang_lib):
        super().__init__()
        self.lang_lib = lang_lib
        self.fn_name = ""
        self.is_in_exec_mode = False

    def visitFuncContract(self, ctx):
        self.is_in_exec_mode = True
        super().visitFuncContract(ctx)
        self.is_in_exec_mode = False
        return None

    def visitCStatement(self, ctx):
        self.is_in_exec_mode = True
        super().visitFuncContract(ctx)
        self.is_in_exec_mode = False
        return None

    def visitTerm(self, ctx):
        if ctx.polyId() and self.is_in_exec_mode:
            try:
                self.visitPolyId(ctx.polyId())
            except FnNameMeet as _:
                param_list = []
                for term in ctx.term():
                    param_list.append(term.getText())
                raise FnCallMeet(f"{self.fn_name} FnCallMeet", param_list)
        return super().visitTerm(ctx)

    def visitPolyId(self, ctx):
        if ctx.getText().strip() == self.fn_name.strip() and self.is_in_exec_mode:
            # raise ValueError(f"{ctx.getText()}")
            raise FnNameMeet(f"{self.fn_name} call meet!")
        return super().visitPolyId(ctx)

    def get_first_call_position(self, fn_name, param_id, acsl_info, rust_code):
        self.fn_name = fn_name
        contexts = acsl_info["context"]
        acsl_codes = acsl_info["annotation"]
        query_context = None
        param_list = []
        for id, acsl_code in enumerate(acsl_codes):
            input_stream = InputStream(acsl_code)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()
            try:
                self.visit(tree)
            except FnCallMeet as e:
                query_context = contexts[id]
                param_list = e.param_list
                break
        if query_context is None:
            return None
        position = NonTypedItemExtractor(self.lang_lib).query_position(
            query_context, rust_code
        )
        # raise ValueError(f"position:{position}\nparam_list:{param_list}\nparam_id:{param_id}")
        param_expr = param_list[param_id]
        return param_expr, position


class RustTypeAnalyzer:
    @staticmethod
    def is_uninterp_spec_fn_param_slice_type(
        fn_name, param_index, rust_file_path, acsl_info, target_project_dir
    ) -> bool:
        with open(rust_file_path, "r") as f:
            rust_code = f.read()
        dir_path = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.join(dir_path, "../spec/build/my-languages.so")
        param_expr, position = SpecFncCallPositionSearcher(
            lang_lib
        ).get_first_call_position(fn_name, param_index, acsl_info, rust_code)

        rust_items_list = [param_expr]
        insert_line = position[0]
        new_code, start_line, end_line = RustTypeAnalyzer.insert_let_bindings(
            rust_code=rust_code, line_num=insert_line, items=rust_items_list
        )

        with tempfile.NamedTemporaryFile(suffix=".rs", mode="w+", delete=False) as tmp:
            tmp.write(new_code)
            tmp_file_path = tmp.name
        # call rust-analyzer lsp client to get the type of the non-typed items
        lsp_client = RustAnalyzerClient(logger=DummyLogger())
        lsp_client.initialize(target_project_dir)
        lsp_client.copy_source_rs(tmp_file_path)
        lsp_client.did_open()
        resp = lsp_client.inlay_hint(start_line, 0, end_line + 1, 0)
        type_hints = lsp_client.extract_inlay_types(resp)

        audit_list = []
        for type_hint in type_hints:
            # check if type_hint is which we really want.
            if type_hint[0] == position[0] + 1:
                judge_result = TypeClassifier.is_type_slice(type_hint[2])
                audit_list.append((type_hint, judge_result))
                return judge_result
        lsp_client.close()
        os.remove(tmp_file_path)
        # raise ValueError(f"{audit_list}")
        return False

    def __init__(self, lang_lib, logger=None):
        self.parser = TreeSitterParser(lang_lib, logger=logger)
        self.logger = logger
        self.lang_lib = lang_lib
        self.item_extractor = NonTypedItemExtractor(lang_lib=lang_lib, logger=logger)

    def printlog(self, *args, sep=" ", end="\n"):
        msg = sep.join(str(arg) for arg in args) + end
        if self.logger:
            self.logger.info(msg)
        else:
            print(*args, sep=sep, end=end)

    @staticmethod
    def insert_let_bindings(rust_code, line_num, items):
        """
        return: new_code, start_line, end_line
        """
        lines = rust_code.splitlines()

        insert_lines = [
            f"let verus_tmp{i + 1} = {item};" for i, item in enumerate(items)
        ]

        insert_at = line_num + 1
        lines[insert_at:insert_at] = insert_lines

        start_line = insert_at
        end_line = insert_at + len(items) - 1

        # concatenate the lines back into a single string
        new_code = "\n".join(lines)
        return new_code, start_line, end_line

    def find_function_brace_line(self, node, rust_code):
        if node.type == "function_item":
            for child in node.children:
                if child.type == "block":
                    start_byte = child.start_byte
                    brace_line = rust_code[:start_byte].count(b"\n") + 1
                    return brace_line
        for child in node.children:
            line = self.find_function_brace_line(child, rust_code)
            if line:
                return line
        return None

    def type_analysis(self, rust_file_path, acsl_info, target_project_dir):
        """
        rust_file_path: the path of the rust file
        acsl_info: the acsl info of the c file
        target_project_dir: the path of the project that contains the rust file
        return: the type of the non-typed items, and the corresponding index(the i-th acsl annotation in the file)
        e.g. [
            {"index":0,"item":"x","type":"i32"},
            {"index":1,"item":"y","type":"i32"},
            {"index":2,"item":"z","type":"i32"},
        ]
        """
        func_sigs = self.parser.rust_extract_function_signatures(
            rust_file_path=rust_file_path
        )
        self.parser.print_function_signatures(func_sigs)
        # for acsl in acsl_info["annotation"]:
        #     self.printlog(f"acsl: {acsl}")
        items = self.item_extractor.extract_non_typed_items(
            acsl_info=acsl_info, rust_file_path=rust_file_path
        )

        with open(rust_file_path, "r") as f:
            rust_code = f.read()

        typed_items = []
        type_classifier = TypeClassifier()

        for item in items:
            if not isinstance(item["position"], tuple):
                try:
                    typed_items.append(
                        {
                            "index": item["index"],
                            "func_name": item["position"],
                            "items": func_sigs[item["position"]],
                        }
                    )
                except Exception:
                    pass
                continue
            if len(item["items"]) == 0:
                continue
            rust_items_list = list(item["items"])
            insert_line = item["position"][0]
            new_code, start_line, end_line = self.insert_let_bindings(
                rust_code=rust_code, line_num=insert_line, items=rust_items_list
            )

            with tempfile.NamedTemporaryFile(
                suffix=".rs", mode="w+", delete=False
            ) as tmp:
                tmp.write(new_code)
                tmp_file_path = tmp.name
            # call rust-analyzer lsp client to get the type of the non-typed items
            lsp_client = RustAnalyzerClient(logger=self.logger)
            lsp_client.initialize(target_project_dir)
            lsp_client.copy_source_rs(tmp_file_path)
            lsp_client.did_open()
            resp = lsp_client.inlay_hint(start_line, 0, end_line + 1, 0)
            type_hints = lsp_client.extract_inlay_types(resp)

            for type_hint in type_hints:
                #! Needed to audit
                type_class = type_classifier.classify_type(type_hint[2])
                typed_items.append(
                    {
                        "index": item["index"],
                        "item": rust_items_list[int(type_hint[0]) - int(start_line)],
                        "type": type_class,
                    }
                )
            lsp_client.close()
            os.remove(tmp_file_path)

        return typed_items

    def is_typed_items_in_contract(typed_items):
        if "func_name" in typed_items.keys():
            return True
        return False

    def is_type_str_ref(type_kind):
        if type_kind == TypeKind.IMMUT_STR or type_kind == TypeKind.MUT_STR:
            return True
        return False

    def is_type_slice(type_kind):
        if (
            type_kind == TypeKind.MUT_SLICE
            or type_kind == TypeKind.IMMUT_SLICE
            or type_kind == TypeKind.IMMUT_STR
            or type_kind == TypeKind.MUT_STR
        ):
            return True
        return False

    def is_type_mut(type_kind):
        if (
            type_kind == TypeKind.MUT_VALUE
            or type_kind == TypeKind.MUT_SLICE
            or type_kind == TypeKind.MUT_STR
        ):
            return True
        return False

    def is_type_option(type_kind):
        if type_kind == TypeKind.OPTION:
            return True
        return False


if __name__ == "__main__":
    pass
