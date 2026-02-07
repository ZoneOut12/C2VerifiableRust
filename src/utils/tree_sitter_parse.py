import re
from tree_sitter import Language, Parser
from dataclasses import dataclass
from typing import List
from enum import Enum


class TypeKind(Enum):
    PRIMITIVE = "primitive"
    IMMUT_VALUE = "immut_value"
    IMMUT_SLICE = "immut_slice"
    IMMUT_STR = "immut_str"
    MUT_VALUE = "mut_value"
    MUT_SLICE = "mut_slice"
    MUT_STR = "mut_str"
    OPTION = "option"
    OTHER = "other"


PRIMITIVES = {
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
    "bool",
    "char",
    "f32",
    "f64",
}


class TypeClassifier:
    def __init__(self):
        pass

    @staticmethod
    def is_type_slice(type_str: str) -> bool:
        s = type_str.strip()
        if re.fullmatch(r"&\s*\[[^\]]*\]", s):
            return True
        elif re.fullmatch(r"&\s*mut\s*\[[^\]]*\]", s):
            return True
        else:
            return False

    def classify_type(self, type_str: str) -> TypeKind:
        s = type_str.strip()

        if s in PRIMITIVES:
            return TypeKind.PRIMITIVE
        if re.fullmatch(r"Option\s*<.*>", s):
            return TypeKind.OPTION
        if s == "&str" or s == "&String":
            return TypeKind.IMMUT_STR
        if s == "&mut str" or s == "&mut String":
            return TypeKind.MUT_STR
        if re.fullmatch(r"&\s*\[[^\]]*\]", s):
            return TypeKind.IMMUT_SLICE
        if re.fullmatch(r"&\s*mut\s*\[[^\]]*\]", s):
            return TypeKind.MUT_SLICE
        if s.startswith("&mut "):
            return TypeKind.MUT_VALUE
        if s.startswith("&"):
            return TypeKind.IMMUT_VALUE
        return TypeKind.OTHER


class TreeSitterParser:
    def __init__(self, lang_lib, logger=None):
        self.lang_lib = lang_lib
        self.logger = logger
        self.func_sigs = {}

    def get_parser(self, lang):
        LANGUAGE_LIB = self.lang_lib
        parser = Parser()
        if lang == "c":
            parser.set_language(Language(LANGUAGE_LIB, "c"))
            return parser
        elif lang == "rust":
            parser.set_language(Language(LANGUAGE_LIB, "rust"))
            return parser
        else:
            raise ValueError(f"Unsupported language: {lang}")

    def printlog(self, *args, sep=" ", end="\n"):
        msg = sep.join(str(arg) for arg in args) + end
        if self.logger:
            self.logger.info(msg)
        else:
            print(*args, sep=sep, end=end)

    def print_node_fields(self, node, source_code, indent=""):
        self.printlog(
            f"{indent}- {node.type} -> {source_code[node.start_byte:node.end_byte].decode('utf-8').strip()}"
        )

        for i, child in enumerate(node.children):
            field_name = node.field_name_for_child(i)
            field_info = f" [field_name: {field_name}]" if field_name else ""
            self.printlog(f"{indent}  |- {child.type}{field_info}")
            self.print_node_fields(child, source_code, indent + "    ")

    def tree_sitter_parse_c(self, file_path):
        source_code = ""
        with open(file_path, "r") as f:
            source_code = f.read().encode("utf8")
        LANGUAGE_LIB = self.lang_lib
        C_LANGUAGE = Language(LANGUAGE_LIB, "c")
        parser = Parser()
        parser.set_language(C_LANGUAGE)
        tree = parser.parse(source_code)
        root_node = tree.root_node
        self.print_node_fields(root_node, source_code)

    def tree_sitter_parse_rust(self, file_path):
        source_code = ""
        with open(file_path, "r") as f:
            source_code = f.read().encode("utf8")
        LANGUAGE_LIB = self.lang_lib
        RUST_LANGUAGE = Language(LANGUAGE_LIB, "rust")
        parser = Parser()
        parser.set_language(RUST_LANGUAGE)
        tree = parser.parse(source_code)
        root_node = tree.root_node
        self.print_node_fields(root_node, source_code)

    def get_actual_param_type(self, func_name, var_name):
        params = self.func_sigs[func_name]
        for param in params:
            if param.name == var_name:
                return param.type.kind
        return TypeKind.OTHER

    def rust_extract_function_signatures(self, rust_file_path):
        source_code = ""
        with open(rust_file_path, "r") as f:
            source_code = f.read().encode("utf8")
        LANGUAGE_LIB = self.lang_lib
        RUST_LANGUAGE = Language(LANGUAGE_LIB, "rust")
        parser = Parser()
        parser.set_language(RUST_LANGUAGE)
        tree = parser.parse(source_code)
        root_node = tree.root_node
        self.func_sigs = self.rust_add_function_signature(root_node, source_code)
        return self.func_sigs

    def rust_add_function_signature(self, node, source_code):
        results = {}
        type_classifier = TypeClassifier()

        def get_text(n):
            return source_code[n.start_byte : n.end_byte].decode()

        for child in node.children:
            if child.type == "function_item":
                fn_name = child.child_by_field_name("name").text.decode()
                parameters = []
                params_node = child.child_by_field_name("parameters")
                for item in params_node.children:
                    if item.type == "parameter":
                        # print(item.text.decode())

                        if item.child_by_field_name("pattern"):
                            # print(item.child_by_field_name('pattern').text.decode())
                            param_name = get_text(item.child_by_field_name("pattern"))
                            param_type_node = item.child_by_field_name("type")
                            # type_info = get_type_info(param_type_node)
                            type_str = get_text(param_type_node)
                            type_class = type_classifier.classify_type(type_str)
                            parameters.append({"name": param_name, "type": type_class})
                return_type_node = child.child_by_field_name("return_type")
                if return_type_node:
                    return_type = get_text(return_type_node)
                    type_class = type_classifier.classify_type(return_type)
                    parameters.append({"name": r"\result", "type": type_class})

                if fn_name is not None:
                    results[fn_name] = parameters

            # Recursively process child nodes
            child_results = self.rust_add_function_signature(child, source_code)
            results.update(child_results)

        return results

    def print_function_signatures(self, signatures):
        for fn_name, params in signatures.items():
            self.printlog(f"Function: {fn_name}")
            for p in params:
                self.printlog(f"  Param: {p["name"]}, Type: {p["type"]}")

    def remove_old_with_stack(s: str) -> str:
        stack = []
        i = 0
        while i < len(s):
            if s[i] != ")":
                stack.append(s[i])
                i += 1
            else:
                content = []
                while stack and stack[-1] != "(":
                    content.append(stack.pop())
                if not stack:
                    raise ValueError("Unmatched parenthesis")
                stack.pop()

                inner = "".join(reversed(content))

                if len(stack) >= 3 and "".join(stack[-3:]) == "old":
                    stack.pop()
                    stack.pop()
                    stack.pop()
                    for ch in inner:
                        stack.append(ch)
                else:
                    stack.append("(")
                    for ch in inner:
                        stack.append(ch)
                    stack.append(")")
                i += 1

        return "".join(stack)


if __name__ == "__main__":
    pass
