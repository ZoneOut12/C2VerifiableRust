from tree_sitter import Language, Parser
import os, sys


class Refactor:
    def __init__(self, logger, lang_lib):
        self.logger = logger
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "rust")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        current_dir = os.path.dirname(os.path.abspath(__file__))
        prelude_path = os.path.join(current_dir, "prelude.txt")
        with open(prelude_path, 'r', encoding='utf-8') as f:
            self.prelude_code_block = f.read()
        pass

    def traverse(self, source_code):
        """Print the type of every node"""
        tree = self.parser.parse(source_code.encode("utf-8"))
        node = tree.root_node
        self.traverse_node(node, source_code.encode("utf-8"))

    def traverse_node(self, node, source_code):
        self.logger.info(
            f"Node type: {node.type}\n Node text: {node.text.decode('utf-8')}"
        )
        for child in node.children:
            self.traverse_node(child, source_code)

    def add_verus_macro(self, source_code, orgin_main_exist=False):
        tree = self.parser.parse(source_code.encode("utf8"))
        byte_code = source_code.encode("utf8")
        root_node = tree.root_node
        result_code = []
        last_index = 0
        is_first_func = True
        is_verus_added = False
        main_index = 0
        # traverse the AST
        for node in root_node.children:
            if node.type == "inner_attribute_item":
                if is_verus_added:
                    result_code.append(byte_code[last_index : node.end_byte].decode())
                else:
                    result_code.append(byte_code[last_index : node.end_byte].decode())
                    # result_code.append(
                    #     "\nuse vstd::prelude::*;\n#[allow(unused_imports)]\nuse vstd::math::*;\nuse vstd::slice::*;\nverus! {\n"
                    # )
                    result_code.append(self.prelude_code_block)
                    is_verus_added = True
                    if orgin_main_exist:
                        result_code.append(byte_code[last_index:].decode())
                        result_code.append("\n} // verus!\n")
                        return "\n".join(result_code)
                last_index = node.end_byte
            elif node.type == "function_item":
                if is_verus_added is False:
                    # result_code.append(
                    #     "\nuse vstd::prelude::*;\n#[allow(unused_imports)]\nuse vstd::math::*;\nuse vstd::slice::*;\nverus! {\n"
                    # )
                    result_code.append(self.prelude_code_block)
                    is_verus_added = True
                    if orgin_main_exist:
                        result_code.append(byte_code[last_index:].decode())
                        result_code.append("\n} // verus!\n")
                        return "\n".join(result_code)

                name_node = node.child_by_field_name("name")
                function_name = byte_code[
                    name_node.start_byte : name_node.end_byte
                ].decode()
                if function_name == "main":
                    main_index = node.start_byte
                    break
            result_code.append(byte_code[last_index : node.end_byte].decode())
            last_index = node.end_byte

        # append `} // verus!` at the file end #, and before function 'main'
        result_code.append("\n} // verus!\n")
        result_code.append(byte_code[main_index:].decode())

        # return the modified code
        return "\n".join(result_code)

    def add_func_res(self, source_code):
        source_code = source_code.encode("utf8")
        tree = self.parser.parse(source_code)
        root_node = tree.root_node

        fn_nodes = []
        new_code_segs = []

        def walk(node):
            if node.type == "function_item":
                fn_nodes.append(node)
            for child in node.children:
                walk(child)

        walk(root_node)
        last_index = 0
        for node in fn_nodes:
            new_code_segs.append(source_code[last_index : node.start_byte].decode())
            name_node = node.child_by_field_name("name")
            return_type_node = node.child_by_field_name("return_type")
            function_name = source_code[
                name_node.start_byte : name_node.end_byte
            ].decode()
            if function_name and return_type_node:
                return_type = source_code[
                    return_type_node.start_byte : return_type_node.end_byte
                ].decode()

                modified_return_type = (
                    f"(result: {return_type})"  # replace `-> T` with `-> (result: T)`
                )
                new_code_segs.append(
                    source_code[node.start_byte : return_type_node.start_byte].decode()
                    + modified_return_type
                    + source_code[return_type_node.end_byte : node.end_byte].decode()
                )
            else:
                new_code_segs.append(
                    source_code[node.start_byte : node.end_byte].decode()
                )
            last_index = node.end_byte
        new_code_segs.append(source_code[last_index:].decode())
        return "\n".join(new_code_segs)

    def get_replacement(self, type_str):
        """Map the libc type to the Rust naive standard type"""
        if type_str == "libc::c_int":
            return "i32"
        elif type_str == "libc::c_uint":
            return "u32"
        elif type_str == "libc::c_char":
            return "i8"
        elif type_str == "libc::c_schar":
            return "i8"
        elif type_str == "libc::c_uchar":
            return "u8"
        elif type_str == "libc::c_short":
            return "i16"
        elif type_str == "libc::c_ushort":
            return "u16"
        elif type_str == "libc::c_long":
            return "i32"
        elif type_str == "libc::c_ulong":
            return "u32"
        elif type_str == "libc::c_longlong":
            return "i64"
        elif type_str == "libc::c_ulonglong":
            return "u64"
        elif type_str == "libc::c_float":
            return "f32"
        elif type_str == "libc::c_double":
            return "f64"
        elif type_str == "libc::size_t":
            return "usize"
        elif type_str == "libc::ssize_t":
            return "isize"
        else:
            return type_str

    def replace_libc_types(self, node, source_code):
        byte_code = source_code.encode("utf8")
        if node.type == "scoped_type_identifier":
            text = byte_code[node.start_byte : node.end_byte].decode()
            return self.get_replacement(text)

        new_code = []
        last_end = node.start_byte
        for child in node.children:
            new_code.append(byte_code[last_end : child.start_byte].decode())
            replacement = self.replace_libc_types(child, source_code)
            new_code.append(
                replacement
                if replacement
                else byte_code[child.start_byte : child.end_byte].decode()
            )
            last_end = child.end_byte

        new_code.append(byte_code[last_end : node.end_byte].decode())
        return "".join(new_code)

    def has_main_function(self, source_code):
        """Check Rust code whether includes `main` function"""
        tree = self.parser.parse(source_code.encode("utf8"))

        root_node = tree.root_node
        for node in root_node.children:
            if node.type == "function_item":
                for child in node.children:
                    if (
                        child.type == "identifier"
                        and child.text.decode("utf-8") == "main"
                    ):
                        return True
        return False

    def add_main_fn(self, source_code):
        # The second return bool value is to serve for LLM
        if not self.has_main_function(source_code):
            return source_code + "\nfn main(){}", False
        else:
            return source_code, True

    def add_DerefSpec_trait(self, source_code):
        deferspec_trait = r"""trait GetrefSpec<T> {
    spec fn getref(&self) -> T;
}

impl<T: Deref> GetrefSpec<T> for T {
    spec fn getref(&self) -> T {
        *self
    }
}

impl<T: Deref> GetrefSpec<T> for Option<T> {
    spec fn getref(&self) -> T {
        (*self)->0
    }
}

"""
        return deferspec_trait + source_code

    def remove_assert_ffi(self, source_code):
        tree = self.parser.parse(source_code.encode("utf8"))
        byte_code = source_code.encode("utf-8")
        root = tree.root_node
        res = ""
        has_assert_ffi = False
        for child in root.children:
            if child.type == "foreign_mod_item":
                for descendant in child.children:
                    if descendant.type == "extern_modifier":
                        lang = byte_code[
                            descendant.start_byte : descendant.end_byte
                        ].decode()
                        if lang != 'extern "C"':
                            break
                    elif descendant.type == "declaration_list":
                        for node in descendant.children:
                            if node.type == "function_signature_item":
                                for n in node.children:
                                    if n.type == "identifier":
                                        func_name = byte_code[
                                            n.start_byte : n.end_byte
                                        ].decode()
                                        # if func_name == "__assert_fail":
                                        if func_name == "verus_assert":
                                            has_assert_ffi = True
                                            res += byte_code[: node.start_byte].decode()
                                            res += byte_code[node.end_byte :].decode()
        if not has_assert_ffi:
            res = source_code
        return res

    def remove_empty_foreign_c_mod(self, source_code):
        """
        After calling "remove_assert_ffi", extern "C" block may be empty.
        Remove the extern "C" block if empty.
        """
        tree = self.parser.parse(source_code.encode("utf8"))
        byte_code = source_code.encode("utf-8")
        root = tree.root_node

        has_signature = False
        last_index = 0
        is_extern_c = True
        for child in root.children:
            if child.type == "foreign_mod_item":
                for descendant in child.children:
                    if descendant.type == "extern_modifier":
                        lang = byte_code[
                            descendant.start_byte : descendant.end_byte
                        ].decode()
                        if lang != 'extern "C"':
                            is_extern_c = False
                            break
                    elif descendant.type == "declaration_list":
                        for node in descendant.children:
                            if node.type != "{" and node.type != "}":
                                has_signature = True

                if not is_extern_c:
                    is_extern_c = True
                    continue
                if not has_signature:
                    res1 = byte_code[0 : child.start_byte].decode()
                    res3 = byte_code[child.end_byte :].decode()
                    return res1, None, res3
                else:
                    res1 = byte_code[0 : child.start_byte].decode()
                    res2 = byte_code[child.start_byte : child.end_byte].decode()
                    res3 = byte_code[child.end_byte :].decode()
                    return res1, res2, res3

        res1 = byte_code[last_index:].decode()
        return res1, None, None

    def extract_extern_c_mod_if_not_empty(self, source_code):
        """
        Extract the extern "C" block if not empty.
        In the meantime, return the code without extern "C" block.
        Return: code without extern "C" block, extern "C" block
        """
        res1, res2, res3 = self.remove_empty_foreign_c_mod(source_code)
        if res2 is not None:
            self.logger.info(f'extern "C" block code:\n{res2}')
            res = res1 + "\n" + res3
            return res, res2
        elif res3 is not None:
            res = res1 + "\n" + res3
            return res, None
        else:
            res = res1
            return res, None

    def add_extern_c_block(self, source_code, extern_c_block):
        """
        Param:
            1. source_code: code with "verus!" macro added
            2. extern_c_block: extern "C" block with nonempty declarations
        Return: source_code with extern_c_block added.
        """
        tree = self.parser.parse(source_code.encode("utf8"))
        byte_code = source_code.encode("utf-8")
        root = tree.root_node
        res = ""
        for node in root.children:
            if node.type == "macro_invocation":
                for child in node.children:
                    if child.type == "identifier":
                        macro_name = byte_code[
                            child.start_byte : child.end_byte
                        ].decode()
                        if macro_name.strip() == "verus":
                            res += byte_code[: node.start_byte].decode()
                            res += "\n" + extern_c_block + "\n"
                            res += byte_code[node.start_byte :].decode()
                            return res
        self.logger.error(
            "[Error] After add_verus_macro refactoring, the code is still withous verus! macro.\n"
        )
        sys.exit(1)

    def llm_add_verus_macro(self, source_code, orgin_main_exist=False):
        byte_code = source_code.encode("utf8")
        result_code = []
        # added code in `llm_add_verus_marco` method.
        # result_code.append(
        #     "use vstd::prelude::*;\n#[allow(unused_imports)]\nuse vstd::math::*;\nuse vstd::slice::*;\nverus! {\n"
        # )
        result_code.append(self.prelude_code_block)

        result_code.append(byte_code.decode())
        result_code.append("\n} // verus!\n")

        # return the modified code
        return "\n".join(result_code)

    def for_loop_refactor(self, source_code):
        """
        convert `for` loop into `while` loop in Rust code.
        """
        source_code = source_code.encode("utf8")
        tree = self.parser.parse(source_code)
        root_node = tree.root_node

        def find_for_loops(node):
            if node.type == "for_expression":
                yield node
            for child in node.children:
                yield from find_for_loops(child)

        for_nodes = list(find_for_loops(root_node))
        # for_nodes.sort(key=lambda n: n.start_byte, reverse=True)

        res = ""
        last_loop_end_byte = 0

        for node in for_nodes:
            pattern = node.child_by_field_name("pattern")  # i
            iterator = node.child_by_field_name("value")  # 0..n
            body = node.child_by_field_name("body")  # {...}

            var = source_code[pattern.start_byte : pattern.end_byte].decode()
            range_expr = source_code[iterator.start_byte : iterator.end_byte].decode()
            body_code = source_code[body.start_byte : body.end_byte].decode()

            # deal with Range expression：currently only support `a..b`
            if ".." not in range_expr:
                continue  # Currently skip complex iterator expression

            start, end = map(str.strip, range_expr.split("..", 1))

            # preserve braces and insert `while` content
            new_loop = (
                f"let mut {var} = {start};\n"
                f"while {var} < {end} {body_code}\n"
                f"    {var} += 1;\n"
                f"}}"
            )

            # replace original rust code `for` loop with `while` loop
            res += source_code[last_loop_end_byte : node.start_byte].decode() + new_loop
            last_loop_end_byte = node.end_byte

        res += source_code[last_loop_end_byte:].decode()
        return res

    def add_attribute_macro(self, source_code):
        """
        For every function, insert `#[verifier::loop_isolation(false)]` before funciton.
        """
        loop_isolation_attr = "#[verifier::loop_isolation(false)]\n#[verifier::exec_allows_no_decreases_clause]\n"
        external_attr = "#[verifier::external_body]\n"

        source_code = source_code.encode("utf8")
        tree = self.parser.parse(source_code)
        root_node = tree.root_node

        function_nodes = []

        def is_unimplemented_call(node):
            if node.type != "macro_invocation":
                for child in node.children:
                    if is_unimplemented_call(child):
                        return True
                return False
            macro_name = source_code[
                node.child_by_field_name("macro")
                .start_byte : node.child_by_field_name("macro")
                .end_byte
            ]
            return macro_name.decode("utf-8") == "unimplemented"

        def collect_functions(node):
            if node.type == "function_item":
                body = node.child_by_field_name("body")
                if body and body.named_child_count == 1:
                    only_stmt = body.named_children[0]
                    if is_unimplemented_call(only_stmt):
                        function_nodes.append((0, node))
                    else:
                        function_nodes.append((1, node))
                else:
                    function_nodes.append((1, node))
            for child in node.children:
                collect_functions(child)

        collect_functions(root_node)
        result_code = []
        last_func_end_byte = 0
        for is_implemented, fn in function_nodes:
            result_code.append(source_code[last_func_end_byte : fn.start_byte].decode())
            if is_implemented:
                result_code.append(
                    loop_isolation_attr
                    + source_code[fn.start_byte : fn.end_byte].decode()
                )
            else:
                result_code.append(
                    external_attr + source_code[fn.start_byte : fn.end_byte].decode()
                )
            last_func_end_byte = fn.end_byte
        result_code.append(source_code[last_func_end_byte:].decode())

        return "\n".join(result_code)

    def static_item_refactor(self, source_code):
        """
        Insert 'exec' before static item.
        Just as `exec static x: u64 = 0;`
        """
        tree = self.parser.parse(bytes(source_code, "utf8"))
        source_code = bytes(source_code, "utf8")
        root = tree.root_node

        result_code = []
        static_nodes = []

        def walk(node):
            if node.type == "static_item":
                static_nodes.append(node)
            for child in node.children:
                walk(child)

        walk(root)

        insertions = []
        last_index = 0
        for node in static_nodes:
            for child in node.children:
                if child.type == "static":
                    result_code.append(
                        source_code[last_index : node.start_byte].decode()
                    )
                    result_code.append(
                        "exec"
                        + r" "
                        + source_code[node.start_byte : node.end_byte].decode()
                    )
                    last_index = node.end_byte
                    break

        result_code.append(source_code[last_index:].decode())
        return "\n".join(result_code)

    def c2rust_main(self, file_path, output_path=None):
        source_code = ""
        with open(file=file_path) as f:
            source_code = f.read()
        tree = self.parser.parse(source_code.encode("utf8"))
        root_node = tree.root_node
        res = self.replace_libc_types(root_node, source_code)
        # sequential order could not be changed
        res = self.remove_assert_ffi(res)
        res, extern_c_block = self.extract_extern_c_mod_if_not_empty(res)

        res = self.add_func_res(res)
        # sequential order could not be changed
        res, _ = self.add_main_fn(res)
        res = self.add_verus_macro(res)
        if extern_c_block is not None:
            res = self.add_extern_c_block(res, extern_c_block)

        if not output_path:
            dir_name, base_name = os.path.split(file_path)
            new_name = "refactored_" + base_name
            output_path = os.path.join(dir_name, new_name)

        with open(output_path, "w", encoding="utf-8") as file:
            file.write(res)
        self.logger.info(
            f"**Refactored** C2Rust-transpiled code:\n```rust\n{res}\n```\n"
        )
        return res

    def llm_main(self, file_path, output_path=None):
        source_code = ""
        with open(file=file_path) as f:
            source_code = f.read()

        # rewrite static item into const item in Rust code, if the static item is not modified.
        rewriter = RustStaticToConstRewriter(lang_lib=self.LANGUAGE_LIB)
        source_code = rewriter.replace_static_with_const(source_code)

        source_code = self.add_attribute_macro(source_code)
        source_code = self.static_item_refactor(source_code)

        tree = self.parser.parse(source_code.encode("utf8"))
        root_node = tree.root_node
        res = self.replace_libc_types(root_node, source_code)
        # sequential order could not be changed
        res = self.add_func_res(res)
        res, orgin_main_exist = self.add_main_fn(res)
        res = self.llm_add_verus_macro(res, orgin_main_exist=orgin_main_exist)

        if not output_path:
            dir_name, base_name = os.path.split(file_path)
            new_name = "refactored_" + base_name
            output_path = os.path.join(dir_name, new_name)

        with open(output_path, "w", encoding="utf-8") as file:
            file.write(res)
        self.logger.info(f"**Refactored** LLM-transpiled code:\n```rust\n{res}\n```\n")
        return res


class RustStaticToConstRewriter:
    def __init__(self, lang_lib):
        RUST_LANGUAGE = Language(lang_lib, "rust")
        self.parser = Parser()
        self.parser.set_language(RUST_LANGUAGE)

    def replace_static_with_const(self, code: str) -> str:
        tree = self.parser.parse(code.encode("utf8"))

        def get_static_variables(tree, code):
            static_vars = []

            def walk(node):
                if node.type == "static_item":
                    name_node = node.child_by_field_name("name")
                    static_vars.append(
                        {
                            "name": code[name_node.start_byte : name_node.end_byte],
                            "start": node.start_byte,
                            "end": node.end_byte,
                        }
                    )
                for child in node.children:
                    walk(child)

            walk(tree.root_node)
            return static_vars

        def is_variable_modified(var_name, tree, code):
            modified = False

            def walk(node):
                nonlocal modified
                # Direct assignment: VAR = ...
                if node.type == "assignment_expression":
                    lhs = node.child_by_field_name("left")
                    if lhs and var_name in code[lhs.start_byte : lhs.end_byte]:
                        modified = True
                # Dereference assignment: *VAR = ...
                if node.type == "unary_expression":
                    op_node = node.child_by_field_name("operator")
                    expr_node = node.child_by_field_name("argument")
                    if (
                        op_node
                        and expr_node
                        and op_node.type == "*"
                        and var_name in code[expr_node.start_byte : expr_node.end_byte]
                    ):
                        modified = True
                for child in node.children:
                    walk(child)

            walk(tree.root_node)
            return modified

        def do_replacement(code, static_vars):
            modified_code = code
            offset = 0
            for var in static_vars:
                before = modified_code[: var["start"] + offset]
                middle = modified_code[var["start"] + offset : var["end"] + offset]
                after = modified_code[var["end"] + offset :]
                if middle.lstrip().startswith("static mut"):
                    new_middle = middle.replace("static mut", "const", 1)
                else:
                    new_middle = middle.replace("static", "const", 1)

                offset += len(new_middle) - len(middle)
                modified_code = before + new_middle + after
            return modified_code

        static_vars = get_static_variables(tree, code)
        readonly_vars = [
            var
            for var in static_vars
            if not is_variable_modified(var["name"], tree, code)
        ]
        return do_replacement(code, readonly_vars)


if __name__ == "__main__":
    pass
