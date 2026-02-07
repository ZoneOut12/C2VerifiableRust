import os, re
from enum import Enum
from collections import defaultdict
from tree_sitter import Language, Parser
from antlr4 import InputStream, CommonTokenStream
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor


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


class SpecDetector(ACSLParserVisitor):
    def __init__(self):
        super().__init__()
        self.transform_error_set = set()
        self.annotation_level_spec_data = {}
        self.file_level_spec_data = {}
        self.eliminated_specs = {}

    def detect(self, acsl_code):
        self.transform_error_set.clear()
        input_stream = InputStream(acsl_code)
        lexer = ACSLLexer(input_stream)
        token_stream = CommonTokenStream(lexer)
        parser = ACSLParser(token_stream)
        tree = parser.acsl()
        self.visit(tree)
        return self.transform_error_set

    def visitGhostCode(self, ctx):
        # self.transform_error_set.add(TransformError.GhostCode)
        return super().visitGhostCode(ctx)

    def visitTerm(self, ctx):
        if ctx.AT():
            self.transform_error_set.add(TransformError.At)
        return super().visitTerm(ctx)

    def visitBinder(self, ctx):
        supported_type_set = {
            "integer",
            "int",
            "size_t",
            "unsigned",
            "int*",
            "boolean",
            "char*",
            "char",
        }
        if ctx.logicAtomicType().getText().strip() not in supported_type_set:
            self.transform_error_set.add(TransformError.UnsupportedType)
        return super().visitBinder(ctx)

    def visitAssignsClause(self, ctx: ACSLParser.AssignsClauseContext):
        if self.eliminated_specs.get("assigns") is None:
            self.eliminated_specs["assigns"] = 0
        self.eliminated_specs["assigns"] += 1
        return super().visitAssignsClause(ctx)

    def visitLoopAssigns(self, ctx: ACSLParser.LoopAssignsContext):
        if self.eliminated_specs.get("assigns") is None:
            self.eliminated_specs["assigns"] = 0
        self.eliminated_specs["assigns"] += 1
        return super().visitLoopAssigns(ctx)

    def visitPred(self, ctx):
        if ctx.SEPARATED():
            if self.eliminated_specs.get("separated") is None:
                self.eliminated_specs["separated"] = 0
            self.eliminated_specs["separated"] += 1
        elif ctx.VALID() or ctx.VALIDREAD():
            if self.eliminated_specs.get("validity") is None:
                self.eliminated_specs["validity"] = 0
            self.eliminated_specs["validity"] += 1
        return super().visitPred(ctx)

    def visitTerminatesClause(self, ctx):
        self.transform_error_set.add(TransformError.TerminatesClause)
        return super().visitTerminatesClause(ctx)

    def visitAxiomaticDecl(self, ctx):
        # self.transform_error_set.add(TransformError.AxiomaticDecl)
        return super().visitAxiomaticDecl(ctx)

    def visitReadsClause(self, ctx):
        self.transform_error_set.add(TransformError.ReadsClause)
        return super().visitReadsClause(ctx)

    def visitInductiveDef(self, ctx):
        # self.transform_error_set.add(TransformError.InductiveDef)
        return super().visitInductiveDef(ctx)

    def visitTypeVar(self, ctx):
        if ctx.getText().strip() == "real":
            self.transform_error_set.add(TransformError.UnsupportedType)
        return super().visitTypeVar(ctx)

    def visitLabelBinders(self, ctx):
        self.transform_error_set.add(TransformError.Labels)
        return super().visitLabelBinders(ctx)

    def merge_dicts_add(self, d1, d2):
        merged = d1.copy()
        for key, value in d2.items():
            merged[key] = merged.get(key, 0) + value
        return merged

    def get_eliminated_specs(self):
        res = self.eliminated_specs.copy()
        self.eliminated_specs.clear()
        return res

    def remove_non_acsl_comments(self, code):
        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)
        return code

    def extract_acsl(self, c_file_path, lang_lib):
        with open(c_file_path, "r") as f:
            code = f.read()
        code = self.remove_non_acsl_comments(code)
        LANGUAGE_LIB = lang_lib
        C_LANGUAGE = Language(LANGUAGE_LIB, "c")
        parser = Parser()
        parser.set_language(C_LANGUAGE)
        tree = parser.parse(code.encode("utf8"))
        root_node = tree.root_node
        acsl_annots = []

        def traverse(node):
            nonlocal acsl_annots
            if node.type == "comment":
                acsl_annots.append(node.text.decode("utf-8"))
            for child in node.children:
                traverse(child)

        traverse(root_node)
        return acsl_annots

    def count_eliminated_specs(self, txt_path, lang_lib):
        with open(txt_path, "r") as f:
            filenames = [line.strip() for line in f.readlines()]

        total_eliminated_specs = {}

        for file_path in filenames:
            if not file_path:
                continue

            acsl_annots = self.extract_acsl(file_path, lang_lib)
            for annot in acsl_annots:
                self.detect(annot)
                total_eliminated_specs = self.merge_dicts_add(
                    total_eliminated_specs, self.get_eliminated_specs()
                )

        return total_eliminated_specs

    def check_file_supported(self, c_file_path, lang_lib):
        acsl_annots = self.extract_acsl(c_file_path, lang_lib)
        for annot in acsl_annots:
            error_set = self.detect(annot)
            # if TransformError.AxiomaticDecl in error_set:
            #     print(c_file_path)
            if len(error_set) > 0:
                return False
        return True

    def total_unmigrated_specifications(self, txt_path, lang_lib):
        with open(txt_path, "r") as f:
            filenames = [line.strip() for line in f.readlines()]

        total_unmigrated_spec_num = 0
        cannot_transform_file_num = 0
        for file_path in filenames:
            if not file_path:
                continue

            acsl_annots = self.extract_acsl(file_path, lang_lib)
            judge = True
            for annot in acsl_annots:
                error_set = self.detect(annot)
                if len(error_set) > 0:
                    judge = False
                    total_unmigrated_spec_num += 1
            if not judge:
                cannot_transform_file_num += 1

        print("-" * 10)
        print(f"Dataset Path: {txt_path}")
        print(cannot_transform_file_num)
        print("Total number of unmigrated specidications:\n")
        print(total_unmigrated_spec_num)
        print("-" * 10)

    def annotation_level_calculate(self, txt_path, lang_lib):
        fail_files = []
        with open(txt_path, "r") as f:
            filenames = [line.strip() for line in f.readlines()]

        non_migratable_spec_num = 0
        cannot_transform_file_num = 0
        for file_path in filenames:
            if not file_path:
                continue

            acsl_annots = self.extract_acsl(file_path, lang_lib)

            judge = True
            for annot in acsl_annots:
                error_set = self.detect(annot)
                if len(error_set) > 0:
                    judge = False
                    non_migratable_spec_num += 1
                for error in error_set:
                    if error.name not in self.annotation_level_spec_data:
                        self.annotation_level_spec_data[error.name] = 0
                    self.annotation_level_spec_data[error.name] += 1
            if not judge:
                fail_files.append(file_path)
                cannot_transform_file_num += 1

        print("-" * 10)
        print(f"Dataset Path: {txt_path}")
        print("Annotation level result:\n")

        print("# Non-migratable Specifications:", non_migratable_spec_num)
        print(self.annotation_level_spec_data)
        print("-" * 10)

    def file_level_calculate(self, txt_path, lang_lib):
        fail_files = []
        with open(txt_path, "r") as f:
            filenames = [line.strip() for line in f.readlines()]

        cannot_transform_file_num = 0
        for file_path in filenames:
            if not file_path:
                continue

            acsl_annots = self.extract_acsl(file_path, lang_lib)
            judge = True
            file_error_set = set()
            for annot in acsl_annots:
                error_set = self.detect(annot)
                if len(error_set) > 0:
                    judge = False
                file_error_set.update(error_set)
            for error in file_error_set:
                if error.name not in self.file_level_spec_data:
                    self.file_level_spec_data[error.name] = 0
                self.file_level_spec_data[error.name] += 1
            if not judge:
                fail_files.append(file_path)
                cannot_transform_file_num += 1

        print("-" * 10)
        print(f"Dataset Path: {txt_path}")
        print("File level result:\n")
        print("# Non-migratable Files:", cannot_transform_file_num)
        print(self.file_level_spec_data)
        print("-" * 10)

    def average_specs_of_file(self, txt_path, lang_lib):
        with open(txt_path, "r") as f:
            filenames = [line.strip() for line in f.readlines()]
        total_specs = 0
        total_files = 0
        for file_path in filenames:
            if not file_path:
                continue
            total_files += 1
            acsl_annots = self.extract_acsl(file_path, lang_lib)
            total_specs += len(acsl_annots)
        average_specs = total_specs / total_files
        print("-" * 10)
        print(f"Dataset Path: {txt_path}")
        print(f"total_files: {total_files}")
        print(f"Average specs: {average_specs}")
        print("-" * 10)
        return average_specs


class DataCollector:
    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)

    def average_lines_of_code(self, txt_file_path):
        total_lines = 0
        total_files = 0

        # Open the txt file containing the list of file paths
        with open(txt_file_path, "r") as file_list:
            # Read each line in the text file (each line is a file path)
            for line in file_list:
                file_path = line.strip()
                if os.path.isfile(file_path):  # Check if the file exists
                    try:
                        with open(file_path, "r") as file:
                            lines = file.readlines()
                            total_lines += len(
                                lines
                            )  # Add the number of lines to total_lines
                            total_files += 1  # Increment the number of files processed
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")
                else:
                    print(f"File not found: {file_path}")

        if total_files > 0:
            average_loc = total_lines / total_files  # Calculate average LoC
            print("-" * 10)
            print(f"Dataset Path: {txt_file_path}")
            print(f"total_files: {total_files}")
            print(f"Average LoC: {average_loc}")  # Print the result
            print("-" * 10)
            return average_loc
        else:
            print("No valid files processed.")
            return 0

    def average_functions_per_file(self, txt_path):
        total_functions = 0
        total_files = 0

        # Open the txt file containing the list of file paths
        with open(txt_path, "r") as file_list:
            # Read each line in the text file (each line is a file path)
            for line in file_list:
                file_path = line.strip()
                if os.path.isfile(file_path):  # Check if the file exists
                    try:
                        with open(file_path, "r") as file:
                            content = file.read()
                            # Parse the content using the parser
                            tree = self.parser.parse(content.encode("utf8"))
                            root_node = tree.root_node

                            # Traverse the tree to count functions
                            functions = self.count_functions(
                                root_node
                            )  # Count function nodes
                            total_functions += functions
                            total_files += 1  # Increment the number of files processed
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")
                else:
                    print(f"File not found: {file_path}")

        if total_files > 0:
            average_functions = (
                total_functions / total_files
            )  # Calculate average functions per file
            print("-" * 10)
            print(f"Dataset Path: {txt_path}")
            print(f"total_files: {total_files}")
            print(
                f"Average functions per file: {average_functions}"
            )  # Print the result
            print("-" * 10)
            return average_functions
        else:
            print("No valid files processed.")
            return 0

    def count_functions(self, node):
        """Recursively count function definitions in the parse tree."""
        total = 0
        # Check if the node is a function definition (depending on tree-sitter's C grammar)
        if node.type == "function_definition":
            total += 1

        # Recursively traverse child nodes
        for child in node.children:
            total += self.count_functions(child)

        return total

    def average_loops_per_file(self, txt_path):
        total_loops = 0
        total_files = 0

        # Open the txt file containing the list of file paths
        with open(txt_path, "r") as file_list:
            # Read each line in the text file (each line is a file path)
            for line in file_list:
                file_path = line.strip()
                if os.path.isfile(file_path):  # Check if the file exists
                    try:
                        with open(file_path, "r") as file:
                            content = file.read()
                            # Parse the content using the parser
                            tree = self.parser.parse(content.encode("utf8"))
                            root_node = tree.root_node

                            # Traverse the tree to count loops
                            loops = self.count_loops(root_node)  # Count loop nodes
                            total_loops += loops
                            total_files += 1  # Increment the number of files processed
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")
                else:
                    print(f"File not found: {file_path}")

        if total_files > 0:
            average_loops = (
                total_loops / total_files
            )  # Calculate average loops per file
            print("-" * 10)
            print(f"Dataset Path: {txt_path}")
            print(f"total_files: {total_files}")
            print(f"Average loops per file: {average_loops}")  # Print the result
            print("-" * 10)
            return average_loops
        else:
            print("No valid files processed.")
            return 0

    def count_loops(self, node):
        """Recursively count loop structures (for, while, do-while) in the parse tree."""
        total = 0
        # Check if the node is a loop (for, while, do-while)
        if node.type in ["for_statement", "while_statement", "do_statement"]:
            total += 1

        # Recursively traverse child nodes
        for child in node.children:
            total += self.count_loops(child)

        return total

    def count_assigns_in_files(self, txt_file):

        assigns_pattern = re.compile(r"\bassigns\b")

        total_assigns_count = 0
        try:
            with open(txt_file, "r", encoding="utf-8") as f:
                files = f.readlines()
                for file_path in files:
                    file_path = file_path.strip()
                    if not file_path:
                        continue
                    try:
                        with open(file_path, "r", encoding="utf-8") as file:
                            content = file.read()
                            assigns_count = len(assigns_pattern.findall(content))
                            total_assigns_count += assigns_count
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")

        except Exception as e:
            print(f"Error reading the txt file {txt_file}: {e}")

        return total_assigns_count

    def count_flags_in_rs_files(self, directory):
        pattern = re.compile(r"\b(flag_assigns|flag_valid|flag_separated)\b")
        counts = defaultdict(int)

        for root, _, files in os.walk(directory):
            for file in files:
                if file.endswith(".rs"):
                    file_path = os.path.join(root, file)
                    try:
                        with open(file_path, "r", encoding="utf-8") as f:
                            content = f.read()
                            matches = pattern.findall(content)
                            for match in matches:
                                counts[match] += 1
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")

        return dict(counts)


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    lang_lib = os.path.abspath(
        os.path.join(script_dir, "../spec/build/my-languages.so")
    )
    bench_txt = os.path.abspath(
        os.path.join(script_dir, "../../data/dataset_path/total_benchmark.txt")
    )
    unsupported_txt = os.path.abspath(
        os.path.join(script_dir, "../../data/dataset_path/unsupported_benchmark.txt")
    )
    spec_detector = SpecDetector()
    # with open(bench_txt, "r") as f:
    #     paths = [line.strip() for line in f.readlines()]
    # for path in paths:
    #     c_path = os.path.abspath(os.path.join(project_root_dir, path))
    #     if not spec_detector.check_file_supported(c_path, lang_lib):
    #         print(path)
    spec_detector.file_level_calculate(unsupported_txt, lang_lib)
    spec_detector.annotation_level_calculate(unsupported_txt, lang_lib)
    # spec_detector.total_unmigrated_specifications(unsupported_txt, lang_lib)
    pass
