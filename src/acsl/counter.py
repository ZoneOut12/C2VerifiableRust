import re, os
from tree_sitter import Language, Parser
from antlr4 import InputStream, CommonTokenStream
from src.spec.extract import ACSLType, ACSLJudger, ACSLResult, GhostCodePreprocessor
from src.spec.transform import TransformError
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser


class RawPointerCounter:
    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.raw_pointer_files = []
        pass

    def get_raw_pointer_files(self):
        return self.raw_pointer_files

    def print_node(self, node):
        print(
            f"Node type: {node.type}, Text: {node.text.decode('utf-8')}, Children: {len(node.children)}"
        )
        for child in node.children:
            self.print_node(child)

    def contains_raw_pointer(self, file_path: str) -> bool:
        """
        Check if the file contains raw pointers.
        Args:
            file_path (str): The path to the file.
        Returns:
            bool: True if the file contains raw pointers, False otherwise.
        """
        with open(file_path, "r", encoding="utf-8") as file:
            code = file.read()
        tree = self.parser.parse(code.encode("utf-8"))
        root_node = tree.root_node
        if self.detect_node_has_raw_pointer(root_node):
            self.raw_pointer_files.append(file_path)
            return True
        else:
            return False

    def detect_node_has_raw_pointer(self, node):
        if node.type == "pointer_declarator":
            return True
        for child in node.children:
            if self.detect_node_has_raw_pointer(child):
                return True
        return False


class TransformErrorCounter:
    """
    Count specification types which are not supported for migration
    """

    def __init__(self):
        self.counts = {
            "At": 0,
            "InductiveDef": 0,
            "AxiomaticDecl": 0,
            "UnsupportedType": 0,
            "ReadsClause": 0,
            "TerminatesClause": 0,
            "ParamIsPointerType": 0,
            "GhostCode": 0,
            "Labels": 0,
            "Others": 0,
        }

    def copy(self):
        new_counter = TransformErrorCounter()
        new_counter.counts = self.counts.copy()
        return new_counter

    def items(self):
        return self.counts.items()

    def get(self, key, default=None):
        return self.counts.get(key, default)

    def __getitem__(self, key):
        return self.counts[key]

    def __setitem__(self, key, value):
        self.counts[key] = value

    def update(self, error: TransformError):
        if error == TransformError.At:
            self.counts["At"] += 1
        elif error == TransformError.InductiveDef:
            self.counts["InductiveDef"] += 1
        elif error == TransformError.AxiomaticDecl:
            self.counts["AxiomaticDecl"] += 1
        elif error == TransformError.UnsupportedType:
            self.counts["UnsupportedType"] += 1
        elif error == TransformError.ReadsClause:
            self.counts["ReadsClause"] += 1
        elif error == TransformError.TerminatesClause:
            self.counts["TerminatesClause"] += 1
        elif error == TransformError.ParamIsPointerType:
            self.counts["ParamIsPointerType"] += 1
        elif error == TransformError.Labels:
            self.counts["Labels"] += 1
        elif error == TransformError.GhostCode:
            self.counts["GhostCode"] += 1
        else:
            self.counts["Others"] += 1

    def get_counts(self):
        return self.counts


class ACSLTypeJudger(ACSLJudger):
    """
    Inherit from ACSLJuder.
    In addition, classify and count the logic definitions in the axiomatic block.
    """

    def __init__(self):
        super().__init__()

    def visitCExternalDeclaration(self, ctx):
        counts = {
            "logicConstDef": 0,
            "logicFunctionDef": 0,
            "logicPredicateDef": 0,
            "lemmaDef": 0,
            "inductiveDef": 0,
            "axiomaticDecl": 0,
        }
        for logicdef in ctx.logicDef():
            counts[self.visitLogicDef(logicdef)] += 1
            if logicdef.axiomaticDecl():
                counts_in_axiom_block = self.visitAxiomaticDecl(
                    logicdef.axiomaticDecl()
                )
                if counts_in_axiom_block:
                    counts = {
                        k: counts.get(k, 0) + counts_in_axiom_block.get(k, 0)
                        for k in set(counts) | set(counts_in_axiom_block)
                    }
        return ACSLResult(type=ACSLType.LOGICDEF, counts=counts)

    def visitAxiomaticDecl(self, ctx):
        if ctx.logicDecl():
            counts_in_axiom_block = {
                "logicConstDef": 0,
                "logicFunctionDef": 0,
                "logicPredicateDef": 0,
                "lemmaDef": 0,
                "inductiveDef": 0,
                "axiomaticDecl": 0,
            }
            for logicdecl in ctx.logicDecl():
                if logicdecl.logicDef():
                    counts_in_axiom_block[self.visitLogicDef(logicdecl.logicDef())] += 1
                elif logicdecl.logicConstDecl():
                    counts_in_axiom_block["logicConstDef"] += 1
                elif logicdecl.logicFunctionDecl():
                    counts_in_axiom_block["logicFunctionDef"] += 1
                elif logicdecl.logicPredicateDecl():
                    counts_in_axiom_block["logicPredicateDef"] += 1
                elif logicdecl.axiomDef():
                    counts_in_axiom_block["lemmaDef"] += 1
                else:
                    raise ValueError(f"`LogicTypeDecl` is not supported yet.")
            return counts_in_axiom_block
        return None


class ACSLTypeCounter:
    judger = ACSLTypeJudger()

    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.counts = {
            "funcContract": 0,
            "loop": 0,
            "assertion": 0,
            "ghostCode": 0,
            "logicConstDef": 0,
            "logicFunctionDef": 0,
            "logicPredicateDef": 0,
            "lemmaDef": 0,
            "inductiveDef": 0,
            "axiomaticDecl": 0,
            "others": 0,
        }

    def remove_non_acsl_comments(self, file_path):
        with open(file_path, "r", encoding="utf-8") as file:
            code = file.read()
        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)
        return code

    def extract_acsl_comments(self, code: str) -> list:
        tree = self.parser.parse(code.encode("utf-8"))
        root_node = tree.root_node

        acsl_comments = []

        def traverse(node):
            if node.type == "comment":
                text = code[node.start_byte : node.end_byte]
                acsl_comments.append(text)
            for child in node.children:
                traverse(child)

        traverse(root_node)
        return acsl_comments

    def count_acsl_types(self, annotations):

        for annot in annotations:
            input_stream = InputStream(annot)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()

            result = self.judger.visitAcsl(tree)
            if result.type == ACSLType.GHOSTCODE:
                self.counts["ghostCode"] += 1
            elif result.type == ACSLType.ASSERTION:
                self.counts["assertion"] += 1
            elif result.type == ACSLType.LOOP:
                self.counts["loop"] += 1
            elif result.type == ACSLType.CONTRACT:
                self.counts["funcContract"] += 1
            elif result.type == ACSLType.LOGICDEF:
                for key, value in result.counts.items():
                    self.counts[key] += value
            else:
                self.counts["others"] += 1

    def pipeline(self, file_path):
        cleaned_code = self.remove_non_acsl_comments(file_path=file_path)
        deghosted_code = GhostCodePreprocessor.preprocess(
            self.LANGUAGE_LIB, cleaned_code
        )
        acsl_comments = self.extract_acsl_comments(code=deghosted_code)
        self.count_acsl_types(acsl_comments)
        return self.counts

    def getTypeCounts(self):
        return self.counts


if __name__ == "__main__":
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    lang_lib_path = os.path.join(project_root_dir, "./src/spec/build/my-languages.so")
    supported_benchmark = os.path.join(
        project_root_dir, "./data/dataset_path/supported_benchmark.txt"
    )
    total_benchmark = os.path.join(
        project_root_dir, "./data/dataset_path/total_benchmark.txt"
    )
    tutorial_wp = os.path.join(project_root_dir, "./data/dataset_path/tutorial_wp.txt")
    frama_c_problems = os.path.join(
        project_root_dir, "./data/dataset_path/frama_c_problems.txt"
    )
    lms_verify = os.path.join(project_root_dir, "./data/dataset_path/lms-verify.txt")
    autospec = os.path.join(project_root_dir, "./data/dataset_path/autospec.txt")
    with open(total_benchmark, "r") as f:
        filenames = [line.strip() for line in f.readlines()]
    counter = ACSLTypeCounter(lang_lib=lang_lib_path)
    for file_path in filenames:
        counter.pipeline(file_path=file_path)
    print(counter.getTypeCounts())
    pass
