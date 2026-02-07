import re
from tree_sitter import Language, Parser
from src.utils.formatter import VerusFmt


class Merger:
    def __init__(self, logger, lang_lib):
        self.logger = logger
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "rust")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.nomerged_spec = []
        pass

    def traverse(self, source_code):
        """Print the type of every node"""
        tree = self.parser.parse(source_code.encode("utf-8"))
        node = tree.root_node
        self.traverse_node(node)

    def traverse_node(self, node):
        self.logger.info(
            f"Node type: {node.type}\nNode text: {node.text.decode("utf-8")}"
        )
        for child in node.children:
            self.traverse_node(child)

    def extract_code_in_verus(self, source_code):
        tree = self.parser.parse(source_code.encode("utf-8"))
        byte_code = source_code.encode("utf-8")
        root = tree.root_node
        code_in_verus = ""
        verus_start_index = 0
        verus_end_index = 0
        for node in root.children:
            if node.type == "macro_invocation":
                for child in node.children:
                    if child.type == "identifier":
                        macro_name = byte_code[
                            child.start_byte : child.end_byte
                        ].decode()
                        if macro_name.strip() != "verus":
                            break
                    elif child.type == "token_tree":
                        for n in child.children:
                            if n.type == "{":
                                verus_start_index = n.end_byte
                            elif n.type == "}":
                                verus_end_index = n.start_byte
                        code_in_verus = byte_code[
                            verus_start_index:verus_end_index
                        ].decode()
        return code_in_verus, verus_start_index, verus_end_index

    def extract_assert_annotation(self, context, verus_code):
        """
        extract the 'assert' verus proof annotation from verus_code segments, according to the context info.
        """
        # self.logger.error(f"{len(context)}\n{len(verus_code)}\n")
        assert_annots = []
        for i, item in enumerate(context):
            if item["assert_id"] is not None and item["assert_id"] > 0:
                self.logger.info(f"Verus assert code:\n{verus_code[i]}\n")
                assert_annots.append(verus_code[i])
        return assert_annots

    def merge_logicDef(self, rust_code, verus_info):
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        contexts = verus_info["context"]
        verus_codes = verus_info["annotation"]

        code_segs = []
        for id, context in enumerate(contexts):
            if context["func_name"] == None:
                self.nomerged_spec.remove(verus_codes[id])
                code_segs.append("/*\n" + verus_codes[id] + "*/\n")

        res = "\n".join(code_segs) + rust_code

        return res

    def llm_merge_assert(self, rust_code, verus_info):
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        assert_annots = self.extract_assert_annotation(
            verus_info["context"], verus_info["annotation"]
        )
        code_segs = []
        assert_index = 0
        last_byte = 0

        def assert_traverse(rust_code, node, assert_annots):
            nonlocal code_segs, assert_index, last_byte
            if node.start_byte > last_byte:
                code_segs.append(
                    rust_code.encode("utf-8")[last_byte : node.start_byte].decode()
                )
                last_byte = node.start_byte
            if node.type == "line_comment":
                pattern = re.compile(r"//\s*verus_assert\((\d+)\);?")
                match = pattern.match(node.text.decode("utf-8").strip())
                if match:
                    num = int(match.group(1))
                    assert_index += 1
                    self.logger.warning(
                        f"Actually merged assert index:{assert_index}\nExpected assert index:{num}\n"
                    )
                    last_byte = node.end_byte
                    try:
                        code_segs.append("/*" + assert_annots[assert_index - 1] + "*/")
                    except Exception:
                        self.logger.error(
                            f"Error occurred during merging assertion at index {assert_index - 1}\n"
                        )
                    return
            if node.child_count == 0:
                last_byte = node.end_byte
                code_segs.append(
                    rust_code.encode("utf-8")[node.start_byte : node.end_byte].decode()
                )
                return
            for child in node.children:
                assert_traverse(rust_code, child, assert_annots)
            return

        assert_traverse(rust_code, root, assert_annots)
        res = "".join(code_segs)

        ### check if all the assert_specs have been merged.
        for i in range(assert_index):
            if i >= len(assert_annots):
                break
            self.nomerged_spec.remove(assert_annots[i])
        ###

        return res

    def merge_assert(self, rust_code, verus_info):
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        assert_annots = self.extract_assert_annotation(
            verus_info["context"], verus_info["annotation"]
        )
        code_segs = []
        assert_index = 0
        last_byte = 0

        def assert_traverse(rust_code, node, assert_annots):
            nonlocal code_segs, assert_index, last_byte
            if node.start_byte > last_byte:
                code_segs.append(
                    rust_code.encode("utf-8")[last_byte : node.start_byte].decode()
                )
                last_byte = node.start_byte
            if node.type == "expression_statement":
                for component in node.children:
                    if component.type == "call_expression":
                        for child in component.children:
                            if child.type == "identifier":
                                callee = child.text.decode("utf-8")
                                if callee != "verus_assert":
                                    break
                            elif child.type == "arguments":
                                for descendant in child.children:
                                    if descendant.type == "type_cast_expression":
                                        for n in descendant.children:
                                            if n.type == "integer_literal":
                                                assert_index += 1
                                                self.logger.info(
                                                    f"Actually merged assert index:{assert_index}\nExpected assert index:{n.text.decode("utf-8")}\n"
                                                )
                                                last_byte = node.end_byte
                                                code_segs.append(
                                                    "/*"
                                                    + assert_annots[assert_index - 1]
                                                    + "*/"
                                                )
                                                return
            if node.child_count == 0:
                last_byte = node.end_byte
                code_segs.append(
                    rust_code.encode("utf-8")[node.start_byte : node.end_byte].decode()
                )
                return
            for child in node.children:
                assert_traverse(rust_code, child, assert_annots)
            return

        assert_traverse(rust_code, root, assert_annots)
        res = "".join(code_segs)

        # check if all the assert_specs have been merged.
        for i in range(assert_index):
            self.nomerged_spec.remove(assert_annots[i])

        return res

    def merge_function_contract(self, rust_code, verus_info):
        contexts = verus_info["context"]
        verus_codes = verus_info["annotation"]
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        code_segs = []
        last_byte = 0

        def contract_traverse(rust_code, node):
            nonlocal code_segs, last_byte, contexts, verus_codes
            if node.start_byte > last_byte:
                code_segs.append(
                    rust_code.encode("utf-8")[last_byte : node.start_byte].decode()
                )
                last_byte = node.start_byte
            if node.type == "function_item":
                is_insert = False
                verus_spec = None
                for child in node.children:
                    if child.type == "identifier":
                        func_name = child.text.decode("utf-8")
                        for id, context in enumerate(contexts):
                            if (
                                context["func_name"] == func_name
                                and context["loop_id"] == 0
                                and context["assert_id"] == 0
                            ):
                                is_insert = True
                                verus_spec = verus_codes[id]
                    elif child.type == "block":
                        if is_insert:
                            prev_sibling_node = child.prev_sibling
                            code_segs.append(
                                rust_code.encode("utf-8")[
                                    last_byte : prev_sibling_node.end_byte
                                ].decode()
                            )
                            last_byte = prev_sibling_node.end_byte

                            self.nomerged_spec.remove(verus_spec)

                            code_segs.append("\n/*" + verus_spec + "*/\n")
                            code_segs.append(
                                rust_code.encode("utf-8")[
                                    last_byte : node.end_byte
                                ].decode()
                            )
                            last_byte = node.end_byte
                            return
            if node.child_count == 0:
                last_byte = node.end_byte
                code_segs.append(
                    rust_code.encode("utf-8")[node.start_byte : node.end_byte].decode()
                )
                return
            for child in node.children:
                contract_traverse(rust_code, child)
            return

        contract_traverse(rust_code, root)
        res = "".join(code_segs)
        return res

    def merge_loop_annotation(self, rust_code, verus_info):
        contexts = verus_info["context"]
        verus_codes = verus_info["annotation"]
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        code_segs = []
        last_byte = 0
        loop_id = 0
        func_name = ""

        def loop_traverse(rust_code, node):
            nonlocal code_segs, last_byte, contexts, verus_codes, loop_id, func_name
            if node.start_byte > last_byte:
                code_segs.append(
                    rust_code.encode("utf-8")[last_byte : node.start_byte].decode()
                )
                last_byte = node.start_byte
            if node.type == "function_item":
                loop_id = 0
                for child in node.children:
                    if child.type == "identifier":
                        func_name = child.text.decode("utf-8")
            elif (
                node.type == "for_expression"
                or node.type == "while_expression"
                or node.type == "loop_expression"
            ):
                loop_id += 1
                for child in node.children:
                    if child.type == "block":
                        # Usually, body is the last child.
                        prev_sibling_node = child.prev_sibling
                        for id, context in enumerate(contexts):
                            if (
                                context["func_name"] == func_name
                                and context["loop_id"] == loop_id
                                and context["assert_id"] == 0
                            ):
                                code_segs.append(
                                    rust_code.encode("utf-8")[
                                        last_byte : prev_sibling_node.end_byte
                                    ].decode()
                                )
                                last_byte = prev_sibling_node.end_byte
                                self.nomerged_spec.remove(verus_codes[id])
                                code_segs.append("\n/*" + verus_codes[id] + "*/\n")

                                loop_traverse(rust_code, child)
                                return

            if node.child_count == 0:
                # last_byte = node.end_byte
                code_segs.append(
                    rust_code.encode("utf-8")[last_byte : node.end_byte].decode()
                )
                last_byte = node.end_byte
                return
            for child in node.children:
                loop_traverse(rust_code, child)
            return

        loop_traverse(rust_code, root)
        res = "".join(code_segs)
        return res

    def convert_comment_to_verus(self, rust_code):
        tree = self.parser.parse(rust_code.encode("utf-8"))
        root = tree.root_node
        code_segs = []
        last_index = 0

        def comment_traverse(node):
            nonlocal last_index, code_segs
            if node.type == "block_comment":
                comment_text = node.text.decode("utf-8")
                spec_code = comment_text.strip()[2:-2]
                code_segs.append(
                    rust_code.encode("utf-8")[last_index : node.start_byte].decode()
                )
                code_segs.append(spec_code)
                last_index = node.end_byte
            for child in node.children:
                comment_traverse(child)

        comment_traverse(root)
        code_segs.append(rust_code.encode("utf-8")[last_index:].decode())
        res = "".join(code_segs)
        return res

    def get_unmerged_specs(self):
        return self.nomerged_spec

    def insert_broadcast_use_lemmas(self, rust_code, broadcast_use_lemmas):
        """Insert broadcast_use_lemmas at the start of every function body"""
        rust_code_bytes = bytes(rust_code, "utf8")
        tree = self.parser.parse(rust_code_bytes)
        root_node = tree.root_node

        insert_statement = "/* broadcast use " + ",".join(broadcast_use_lemmas) + "; */"
        insert_positions = []

        def visit(node):
            if node.type == "function_item":
                func_name = None
                for child in node.children:
                    if child.type == "identifier":
                        func_name = rust_code_bytes[
                            child.start_byte : child.end_byte
                        ].decode()
                    elif child.type == "block":
                        block_start = child.start_byte
                        block_end = child.end_byte
                        block_text = rust_code_bytes[block_start:block_end].decode()
                        # check if function body is empty
                        inner = block_text.strip()
                        content_inside = inner.lstrip("{").rstrip("}").strip()
                        if func_name.strip() == "main" and not content_inside:
                            continue
                        insert_positions.append(child.start_byte + 1)
            for child in node.children:
                visit(child)

        visit(root_node)

        # Insert from back to front to prevent position displacement
        modified_code = bytearray(rust_code, "utf8")
        for pos in sorted(insert_positions, reverse=True):
            modified_code[pos:pos] = bytes("\n" + insert_statement + "\n", "utf8")

        return modified_code.decode("utf8")

    def merge(
        self, rust_file, verus_info, broadcast_use_lemmas, output_file, is_llm=False
    ):
        """Insert transpiled verus_code into the appropriate place of rust_code"""
        self.logger.info(f"Start to merge verus-code into {rust_file}\n")
        source_code = None
        with open(rust_file) as f:
            source_code = f.read()
        byte_code = source_code.encode("utf-8")
        code, verus_start_index, verus_end_index = self.extract_code_in_verus(
            source_code
        )
        if len(broadcast_use_lemmas) >= 1:
            code = self.insert_broadcast_use_lemmas(code, broadcast_use_lemmas)
        # record specifications which are not merged successfully
        self.nomerged_spec = list(verus_info["annotation"])

        res = self.merge_logicDef(rust_code=code, verus_info=verus_info)
        self.logger.info(f"The code after merging the logic definition:\n{res}\n")

        if is_llm is False:
            res = self.merge_assert(rust_code=res, verus_info=verus_info)
        else:
            res = self.llm_merge_assert(rust_code=res, verus_info=verus_info)

        res = self.merge_function_contract(rust_code=res, verus_info=verus_info)
        res = self.merge_loop_annotation(rust_code=res, verus_info=verus_info)
        self.logger.info(f"The code after merging the loop annotation:\n{res}\n")
        res = self.convert_comment_to_verus(rust_code=res)
        self.logger.info(
            f"The Rust code with all the transformed Verus code merged:\n{res}\n"
        )
        with open(output_file, "w") as file:
            temp = (
                "use vstd::prelude::*;\n#[allow(unused_imports)]\nuse vstd::math::*;\nuse vstd::slice::*;\nverus! {"
                + res
                + "\n}"
            )
            # print(temp)
            file.write(temp)

        VerusFmt(logger=self.logger).run(output_file)
        with open(output_file) as f:
            res = f.read()
        code, _, _ = self.extract_code_in_verus(res)
        complete_code = (
            byte_code[0:verus_start_index].decode()
            + code
            + byte_code[verus_end_index:].decode()
        )
        with open(output_file, "w", encoding="utf-8") as file:
            file.write(complete_code)
        self.logger.info(
            f"**Merged** Rust code, which has both Verus specifications and Rust code:\n```rust\n{complete_code}\n```\n"
        )
        return complete_code


if __name__ == "__main__":
    pass
