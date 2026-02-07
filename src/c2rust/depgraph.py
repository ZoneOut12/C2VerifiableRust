import clang.cindex, os, re
from collections import defaultdict, deque
from tree_sitter import Language, Parser


class DependencyGraphBuilder:
    """
    This class can build an adjacency dependency graph among types, global variables, macros, and functions in a C file.
    """

    def __init__(self, libclang_path, include_args=["-I/usr/include", "-I."]):
        clang.cindex.Config.set_library_file(libclang_path)
        self.include_args = include_args
        # data structures
        self.custom_types = set()
        self.type_deps = defaultdict(set)
        self.type_contents = {}
        self.global_vars = set()
        self.global_vars_deps = defaultdict(set)
        self.global_vars_contents = {}
        self.functions = set()
        self.func_deps = defaultdict(set)
        self.func_contents = {}
        self.undefined_func_contents = {}  # unimplemented!()
        self.macros = set()
        self.macro_deps = defaultdict(set)
        self.macro_contents = {}
        self.spelling_dict = {}
        # self.deps_graph = defaultdict(set)

    def clear(self):
        self.custom_types = set()
        self.type_deps = defaultdict(set)
        self.type_contents = {}
        self.global_vars = set()
        self.global_vars_deps = defaultdict(set)
        self.global_vars_contents = {}
        self.functions = set()
        self.func_deps = defaultdict(set)
        self.func_contents = {}
        self.undefined_func_contents = {}
        self.macros = set()
        self.macro_deps = defaultdict(set)
        self.macro_contents = {}
        self.spelling_dict = {}
        # self.deps_graph = defaultdict(set)

    def is_user_file(self, node):
        if node.location.file:
            return os.path.abspath(str(node.location.file)) == self.filename
        return False

    def get_node_source(self, node):
        if node.extent.start.file is None:
            return ""
        with open(str(node.extent.start.file), "r") as f:
            lines = f.readlines()
        start_line = node.extent.start.line - 1
        end_line = node.extent.end.line

        if start_line == end_line - 1:
            return lines[start_line][
                node.extent.start.column - 1 : node.extent.end.column - 1
            ]

        result = [lines[start_line][node.extent.start.column - 1 :]]
        for i in range(start_line + 1, end_line - 1):
            result.append(lines[i])
        result.append(lines[end_line - 1][: node.extent.end.column - 1])
        return "".join(result)

    def collect_macros(self, code):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        LANGUAGE_LIB = lang_lib
        LANGUAGE = Language(LANGUAGE_LIB, "c")
        parser = Parser()
        parser.set_language(LANGUAGE)
        source_bytes = bytes(code, "utf-8")
        tree = parser.parse(source_bytes)
        root = tree.root_node

        def visit(n):
            if n.type in ("preproc_def", "preproc_function_def"):
                macro_name = n.child_by_field_name("name")
                if macro_name:
                    name = source_bytes[
                        macro_name.start_byte : macro_name.end_byte
                    ].decode("utf-8")
                self.macros.add(name)
                self.macro_contents[name] = n.text.decode()
                deps = set()
                for word in re.findall(r"\b\w+\b", n.text.decode()):
                    if word in self.custom_types:
                        deps.add(word)
                    if word in self.global_vars:
                        deps.add(word)
                    if word in self.functions:
                        deps.add(word)
                self.macro_deps[name] = deps

            for child in n.children:
                visit(child)

        visit(root)

    def collect_global_vars(self, node):
        if node.kind == clang.cindex.CursorKind.VAR_DECL and self.is_user_file(node):
            if node.semantic_parent.kind == clang.cindex.CursorKind.TRANSLATION_UNIT:
                deps = set()

                def visit(n):
                    if (
                        hasattr(n.type, "spelling")
                        and n.type.spelling in self.custom_types
                    ):
                        deps.add(n.type.spelling)
                    if (
                        n.kind == clang.cindex.CursorKind.DECL_REF_EXPR
                        and n.spelling in self.global_vars
                    ):
                        deps.add(n.spelling)
                    for c in n.get_children():
                        visit(c)

                visit(node)

                self.global_vars.add(node.spelling)
                self.global_vars_deps[node.spelling] = deps
                self.global_vars_contents[node.spelling] = self.get_node_source(node)

        for child in node.get_children():
            self.collect_global_vars(child)

    def collect_type_members(self, node, parent_type):
        for child in node.get_children():
            if (
                hasattr(child.type, "spelling")
                and child.type.spelling in self.custom_types
                and child.type.spelling != parent_type
            ):
                self.type_deps[parent_type].add(child.type.spelling)
            self.collect_type_members(child, parent_type)

    def collect_types(self, node):
        if node.kind in (
            clang.cindex.CursorKind.STRUCT_DECL,
            clang.cindex.CursorKind.UNION_DECL,
            clang.cindex.CursorKind.ENUM_DECL,
            clang.cindex.CursorKind.TYPEDEF_DECL,
        ):
            if node.spelling and self.is_user_file(node):
                self.custom_types.add(node.spelling)
                self.type_deps[node.spelling] = set()
                # self.type_contents[node.spelling] = str(node.displayname)
                self.type_contents[node.spelling] = self.get_node_source(node)
                self.collect_type_members(node, node.spelling)
        for child in node.get_children():
            self.collect_types(child)

    def collect_function_deps(self, node):
        if (
            node.kind == clang.cindex.CursorKind.FUNCTION_DECL
            and node.spelling
            and self.is_user_file(node)
        ):
            if node.is_definition() == False:
                self.functions.add(node.spelling)
                self.func_deps[node.spelling] = set()
                self.undefined_func_contents[node.spelling] = self.get_node_source(node)

            else:
                deps = set()

                def visit(n):
                    # type dependency
                    if (
                        hasattr(n.type, "spelling")
                        and n.type.spelling in self.custom_types
                    ):
                        deps.add(n.type.spelling)
                    # function call dependency
                    if n.kind == clang.cindex.CursorKind.CALL_EXPR and n.spelling:
                        deps.add(n.spelling)
                    # global var dependency
                    if (
                        n.kind == clang.cindex.CursorKind.DECL_REF_EXPR
                        and n.spelling in self.global_vars
                    ):
                        deps.add(n.spelling)
                    for c in n.get_children():
                        visit(c)

                visit(node)
                self.functions.add(node.spelling)
                self.func_deps[node.spelling] = deps
                self.func_contents[node.spelling] = self.get_node_source(node)

        for child in node.get_children():
            self.collect_function_deps(child)

    def topo_sort(self, graph):
        indegree = defaultdict(int)
        for node, deps in graph.items():
            indegree[node] += len(deps)
        queue = deque([n for n in graph if indegree[n] == 0])
        sorted_list = []

        while queue:
            n = queue.popleft()
            sorted_list.append(n)
            for node, deps in graph.items():
                if n in deps:
                    indegree[node] -= 1
                    if indegree[node] == 0:
                        queue.append(node)

        if len(sorted_list) != len(graph):
            raise ValueError(f"\n{sorted_list}\n{graph}\nGraph has at least one cycle")

        return sorted_list

    def build(self, filename):
        self.filename = filename
        with open(filename, "r") as f:
            c_code = f.read()
        index = clang.cindex.Index.create()
        tu = index.parse(filename, args=self.include_args)
        self.collect_types(tu.cursor)
        self.collect_global_vars(tu.cursor)
        self.collect_macros(c_code)
        self.collect_function_deps(tu.cursor)
        deps_graph = defaultdict(set)

        # type dependencies
        for t, deps in self.type_deps.items():
            deps_graph[t] = deps
        # global var dependencies
        for g, deps in self.global_vars_deps.items():
            deps_graph[g] = deps
        for m, deps in self.macro_deps.items():
            deps_graph[m] = deps
        # function dependencies
        for f, deps in self.func_deps.items():
            deps_graph[f] = deps
        sorted_units = self.topo_sort(deps_graph)

        c_slices = {}
        slice_deps = {}
        rust_slices = {}
        for item in sorted_units:
            if item in self.type_contents:
                kind = "Type"
                content = self.type_contents[item]
            elif item in self.func_contents:
                kind = "Function"
                content = self.func_contents[item]
            elif item in self.global_vars_contents:
                kind = "Global Variable"
                content = self.global_vars_contents[item]
            elif item in self.macro_contents:
                kind = "Macro"
                content = self.macro_contents[item]
            elif item in self.undefined_func_contents:
                kind = "Undefined Function"
                content = self.undefined_func_contents[item]
            else:
                kind = "Unknown"
                content = item
                raise ValueError(f"{item} of unknown type in dependency graph")
            c_slices[item] = (content, kind)
            deps = deps_graph[item]
            slice_deps[item] = deps
            rust_slices[item] = None
            # print(f"{kind}:\n{content}\n--> depends on {deps}")
        return {
            "c_slices": c_slices,
            "slice_deps": slice_deps,
            "rust_slices": rust_slices,
        }


if __name__ == "__main__":
    libclang_path = "/usr/lib/llvm-14/lib/libclang.so"
    builder = DependencyGraphBuilder(libclang_path)
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    filename = os.path.join(project_root_dir, "data/tutorial_wp/ex-4-change-answer.c")
    res = builder.build(filename)
    print(res["c_slices"])
    print(res["slice_deps"])
    print(res["rust_slices"])
    builder.clear()
