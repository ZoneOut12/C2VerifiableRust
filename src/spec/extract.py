import re, sys, os
from tree_sitter import Language, Parser
from antlr4 import InputStream, CommonTokenStream
from enum import Enum
from dataclasses import dataclass, field
from typing import Dict
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser


class MyException(Exception):
    pass


class ACSLType(Enum):
    OTHERS = 0
    LOOP = 1
    ASSERTION = 2
    CONTRACT = 3
    LOGICDEF = 4
    GHOSTCODE = 5


@dataclass
class ACSLResult:
    type: ACSLType
    counts: Dict[str, int] = field(default_factory=dict)


class ACSLJudger(ACSLParserVisitor):
    def visitFuncContract(self, ctx):
        return ACSLResult(type=ACSLType.CONTRACT)

    def visitCStatement(self, ctx):
        if ctx.assertion():
            return self.visit(ctx.assertion())
        else:
            return ACSLResult(type=ACSLType.LOOP)

    def visitAssertion(self, ctx):
        return ACSLResult(type=ACSLType.ASSERTION)

    def visitLoopAnnot(self, ctx):
        return ACSLResult(type=ACSLType.LOOP)

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
        return ACSLResult(type=ACSLType.LOGICDEF, counts=counts)

    def visitLogicDef(self, ctx):
        if ctx.logicConstDef():
            return "logicConstDef"
        elif ctx.logicFunctionDef():
            return "logicFunctionDef"
        elif ctx.logicPredicateDef():
            return "logicPredicateDef"
        elif ctx.lemmaDef():
            return "lemmaDef"
        elif ctx.inductiveDef():
            return "inductiveDef"
        elif ctx.axiomaticDecl():
            return "axiomaticDecl"
        else:
            return None

    def visitGhostCode(self, ctx):
        return ACSLResult(type=ACSLType.GHOSTCODE)

    def visitAcsl(self, ctx):
        if ctx.funcContract():
            return ACSLResult(type=ACSLType.CONTRACT)
        elif ctx.cStatement():
            return self.visitCStatement(ctx.cStatement())
        elif ctx.cExternalDeclaration():
            return self.visitCExternalDeclaration(ctx.cExternalDeclaration())
        elif ctx.ghostCode():
            return ACSLResult(type=ACSLType.GHOSTCODE)
        else:
            return ACSLResult(type=ACSLType.OTHERS)


class GhostCodePreprocessor:
    """A preprocessor to deghost ghost code in ACSL annotations."""

    @staticmethod
    def deghost_code(source: str) -> str:
        def replace_block(match):
            inner = match.group(1)
            inner = re.sub(r"/@\s*(.*?)\s*@/", r"/*@ \1 */", inner, flags=re.DOTALL)
            return inner.strip()

        def replace_line(match):
            inner = match.group(1)
            inner = re.sub(r"/@\s*(.*?)\s*@/", r"/*@ \1 */", inner, flags=re.DOTALL)
            return inner.strip()

        # remove block ghost code
        result = re.sub(r"/\*@\s*ghost(.*?)\*/", replace_block, source, flags=re.DOTALL)
        # remove line ghost code
        result = re.sub(
            r"//@\s*ghost(.*?)(?=\n|$)", replace_line, result, flags=re.DOTALL
        )
        # finally, remove any remaining \ghost keywords
        result = re.sub(r"\\ghost\b", "", result)
        return result

    @staticmethod
    def preprocess(lang_lib, c_code):
        LANGUAGE = Language(lang_lib, "c")
        parser = Parser()
        parser.set_language(LANGUAGE)
        c_code_bytes = c_code.encode("utf-8")
        tree = parser.parse(c_code_bytes)
        root_node = tree.root_node
        judger = ACSLJudger()
        preprocessed_code = []
        last_index = 0

        def deghost_ghost_code(node):
            nonlocal last_index
            if node.type == "comment":
                acsl_code = node.text.decode("utf-8")
                input_stream = InputStream(acsl_code)
                lexer = ACSLLexer(input_stream)
                token_stream = CommonTokenStream(lexer)
                acsl_parser = ACSLParser(token_stream)
                tree = acsl_parser.acsl()
                if judger.visitAcsl(tree).type == ACSLType.GHOSTCODE:
                    preprocessed_code.append(
                        c_code_bytes[last_index : node.start_byte].decode()
                    )
                    original_code = node.text.decode()
                    deghosted_code = GhostCodePreprocessor.deghost_code(
                        node.text.decode()
                    )
                    preprocessed_code.append(deghosted_code)
                    last_index = node.end_byte
                    # print(original_code)
                    # print("=======>")
                    # print(deghosted_code)
                    pass

            for child in node.children:
                deghost_ghost_code(child)

        deghost_ghost_code(root_node)
        preprocessed_code.append(c_code_bytes[last_index:].decode())
        return "".join(preprocessed_code)


class SpecExtractor:
    judger = ACSLJudger()

    def __init__(self, logger, lang_lib):
        self.logger = logger
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        pass

    def add_includes(self, source_code):
        """Add assert.h to includes"""
        tree = self.parser.parse(source_code.encode("utf-8"))
        root_node = tree.root_node

        has_assert = False
        for child in root_node.children:
            if child.type == "preproc_include":
                include_text = source_code[child.start_byte : child.end_byte].strip()
                match = re.search(r"<(.*?)>", include_text)
                if match.group(1) == "assert.h":
                    has_assert = True
        if not has_assert:
            source_code = "#include <assert.h>\n" + source_code
        return source_code

    def add_virtual_verus_assert_func(self, source_code):
        """Add `extern void verus_assert(int id);` at the beginning of code."""
        return "extern void verus_assert(int id);\n" + source_code

    def traverse(self, source_code):
        """Print the type of every node"""
        tree = self.parser.parse(source_code.encode("utf-8"))
        node = tree.root_node
        self.traverse_node(node)

    def traverse_node(self, node):
        self.logger.info(
            f"Node type: {node.type}\n Node text: {node.text.decode('utf-8')}"
        )
        for child in node.children:
            self.traverse_node(child)

    def remove_comments(self, file_path):
        with open(file_path, "r", encoding="utf-8") as file:
            code = file.read()

        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)

        return code

    def get_function_signature(self, node, is_llm=False):
        """Extract funtion signature of 'function' node, with the use of 'tree-sitter-c'"""
        if node.type != "function_definition" and node.type != "declaration":
            self.logger.error(
                f"[Error] The 'tree-sitter-c' node type is not function definition!\nThe node text is:{node.text.decode('utf-8')}\nThe real node type is:{node.type}\n"
            )
            sys.exit(1)
        return_type_node = None
        declarator_node = None
        for child in node.children:
            if child.type == "primitive_type":
                return_type_node = child
            elif child.type == "function_declarator":
                declarator_node = child
            elif child.type == "pointer_declarator":
                for grandchild in child.children:
                    if grandchild.type == "function_declarator":
                        declarator_node = grandchild
        # obtain return type
        return_type = (
            return_type_node.text.decode("utf-8") if return_type_node else "unknown"
        )
        # obtain function name
        function_name = "unknown"
        parameters = "unknown"
        if declarator_node:
            # function name
            for child in declarator_node.children:
                if child.type == "identifier":
                    function_name_node = child
                elif child.type == "parameter_list":
                    parameter_list_node = child

            function_name = (
                function_name_node.text.decode("utf-8")
                if function_name_node
                else "unknown"
            )

            # parameter list
            parameters = (
                parameter_list_node.text.decode("utf-8")
                if parameter_list_node
                else "()"
            )
        if function_name == "main" and is_llm is False:
            function_name = "main_0"
        # return f"{return_type} {function_name}{parameters}"
        return f"{function_name}"

    def extract(self, code, file_path, is_llm=False):
        """Parse C code and extract ACSL annotations"""
        func_name = ""
        loop_id = 0
        assert_id = 0
        acsl_context = []
        acsl_annotations = []

        def traverse_comment(node):
            """
            Traverse nodes to deal with 'comments' node(ACSL annotations)
            Assigns: Contextual information of ACSL annotations, namely 'acsl_context' variable
            """
            nonlocal func_name, loop_id, assert_id, acsl_context, acsl_annotations, is_llm
            if node.type == "comment":
                acsl_code = node.text.decode("utf-8")
                input_stream = InputStream(acsl_code)
                lexer = ACSLLexer(input_stream)
                token_stream = CommonTokenStream(lexer)
                acsl_parser = ACSLParser(token_stream)
                tree = acsl_parser.acsl()
                if self.judger.visitAcsl(tree).type == ACSLType.GHOSTCODE:
                    self.logger.error(
                        f"[Error] occurs in {file_path}.\nThe **ghostCode** ACSL annotation is not supported yet!\n{acsl_code}\n"
                    )
                    # Currently, do not support transform the /*@ ghost ... */ or //@ ghost ...
                    raise MyException(
                        f"[Error] occurs in {file_path}.\nThe **ghostCode** ACSL annotation is not supported yet!\n{acsl_code}\n"
                    )

                acsl_annotations.append(acsl_code)
                if self.judger.visitAcsl(tree).type == ACSLType.ASSERTION:
                    assert_id += 1
                    res = {"func_name": func_name, "loop_id": 0, "assert_id": assert_id}
                    acsl_context.append(res)
                elif self.judger.visitAcsl(tree).type == ACSLType.LOOP:
                    res = {
                        "func_name": func_name,
                        "loop_id": loop_id + 1,
                        "assert_id": 0,
                    }
                    acsl_context.append(res)
                elif self.judger.visitAcsl(tree).type == ACSLType.CONTRACT:
                    next_sibling = node.next_named_sibling
                    func_name = self.get_function_signature(next_sibling, is_llm)
                    res = {"func_name": func_name, "loop_id": 0, "assert_id": 0}
                    acsl_context.append(res)
                elif self.judger.visitAcsl(tree).type == ACSLType.LOGICDEF:
                    res = {"func_name": None, "loop_id": None, "assert_id": None}
                    acsl_context.append(res)
                else:
                    self.logger.error(
                        f"[Error] Meet unexpected ACSLType:\n{acsl_code}\n"
                    )
                    sys.exit(1)
            elif node.type == "function_definition":
                func_name = self.get_function_signature(node, is_llm)
                loop_id = 0
            elif (
                node.type == "for_statement"
                or node.type == "while_statement"
                or node.type == "do_statement"
            ):
                loop_id += 1

            for child in node.children:
                traverse_comment(child)

        tree = self.parser.parse(code.encode("utf-8"))
        node = tree.root_node
        traverse_comment(node)

        log_info = (
            "Extracted **ACSL annotations** and its corresponding **Context tuple**:\n"
        )
        for i, context in enumerate(acsl_context):
            log_info += "-" * 80 + "\n"
            log_info += f"[Context tuple]: {context}\n[ACSL annotation]:\n{acsl_annotations[i]}\n"
        self.logger.info(log_info)
        return {"context": acsl_context, "annotation": acsl_annotations}

    def replace(self, code, is_llm=False):
        """Replace ACSL annotations with placeholders.
        Here uses assert(i: int)"""
        acsl_pattern = re.compile(r"//@.*|/\*@[\s\S]*?\*/")
        counter = 1

        def add_serial_number(match):
            nonlocal counter  # Declare that counter is from the outer function's scope
            matched_text = match.group()
            # judge this ACSL annotation is Assertion or not
            input_stream = InputStream(matched_text)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()
            if self.judger.visitAcsl(tree).type == ACSLType.ASSERTION:
                if is_llm is False:
                    replacement = f"verus_assert({counter});"
                else:
                    replacement = f"// verus_assert({counter});"
                counter += 1
                return replacement
            else:
                return ""

        code_with_placeholder = re.sub(
            acsl_pattern,
            add_serial_number,
            code,
        )
        return code_with_placeholder

    def get_acsl_annotation_without_ats(self, code):
        """
        Convert ACSL format:
        /*@ ...
          @ ...
          @*/
        To:
        /*@ */
        """

        def convert_acsl_annotation(match):
            content = match.group(1)

            formatted = "\n".join(line.strip() for line in content.split("@"))
            return f"/*@ {formatted} */"

        pattern = r"/\*@\s*(.*?)\s*@\*/"
        output_str = re.sub(pattern, convert_acsl_annotation, code, flags=re.DOTALL)
        self.logger.info(f"Finish converting the ACSL format:\n{output_str}")

        return output_str

    def c2rust_extract_and_replace(self, file_path):
        """extract ACSL annotations and replace them with macros"""
        # remove annotations which are not about ACSL
        code = self.remove_comments(file_path)
        code = self.get_acsl_annotation_without_ats(code)

        code = GhostCodePreprocessor.preprocess(self.LANGUAGE_LIB, code)

        self.logger.info(
            f"**C code**, which has removed non-ACSL comments:\n```c\n{code}\n```\n"
        )
        acsl_part = self.extract(code, file_path=file_path, is_llm=False)
        code_with_placeholder = self.replace(code, is_llm=False)
        self.logger.info(
            f'**C code**, whose assertion ACSL annotations have been replaced with "verus_assert(id);" placeholder:\n```c\n{code_with_placeholder}\n```\n'
        )
        return acsl_part, code_with_placeholder

    def llm_extract_and_replace(self, file_path):
        """extract ACSL annotations and replace them with macros"""
        # remove annotations which are not about ACSL
        code = self.remove_comments(file_path)
        code = self.get_acsl_annotation_without_ats(code)

        code = GhostCodePreprocessor.preprocess(self.LANGUAGE_LIB, code)

        self.logger.info(
            f"**C code**, which has removed non-ACSL comments:\n```c\n{code}\n```\n"
        )
        acsl_part = self.extract(code, file_path=file_path, is_llm=True)
        code_with_placeholder = self.replace(code, is_llm=True)
        self.logger.info(
            f'**C code**, whose assertion ACSL annotations have been replaced with "// verus_assert(id)" placeholder:\n```c\n{code_with_placeholder}\n```\n'
        )
        return acsl_part, code_with_placeholder


if __name__ == "__main__":
    pass
