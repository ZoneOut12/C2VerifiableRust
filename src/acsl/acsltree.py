import re, sys, os
from collections import deque
from tree_sitter import Language, Parser
from antlr4 import InputStream, CommonTokenStream
from src.spec.extract import ACSLJudger, ACSLType
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserListener import ACSLParserListener


class ACSLNode:
    """
    The Node of ACSL Structural Tree is represented by an integer, which is the sequential order of ACSL annotation occurring in the C Code.
    Node "0" represents the root node, which has no actual meaning.
    Param type means the type of the corresponding ACSL annotation.
    """

    def __init__(self, name, type, acsl):
        self.name = name
        self.type = type
        self.children = []
        self.parent = None
        self.acsl = acsl

    def add_child(self, child):
        child.parent = self
        self.children.append(child)

    def remove_child(self, child):
        self.children.remove(child)
        child.parent = None

    def is_leaf(self):
        return len(self.children) == 0


class ACSLStructuralTree:
    """
    Build ACSL Structural Tree
    The content of Nodes representing acsl annotations should be a positive integer.
    """

    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.judger = ACSLJudger()
        self.root = ACSLNode(0, None, acsl=None)
        self.cur_acsl_order = 0
        self.cur_parent = self.root
        self.next_sibling_is_visited = False
        pass

    def remove_non_acsl_comments(self, code):
        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)
        return code

    def find_first_body_node(self, node):
        """
        Use BFS to find the first body node.
        """
        if node.child_by_field_name("body"):
            return node.child_by_field_name("body")
        queue = deque()
        for child in node.children:
            queue.append(child)
        while queue:
            current = queue.popleft()
            if current.child_by_field_name("body"):
                return current.child_by_field_name("body")
            else:
                for child in current.children:
                    queue.append(child)
        return None

    def traverse_acsl_annotations(self, node):
        """
        Traverse nodes to deal with 'comments' node(ACSL annotations)
        DFS.
        """
        if node.type == "comment":
            self.cur_acsl_order += 1
            acsl_code = node.text.decode("utf-8")
            input_stream = InputStream(acsl_code)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            acsl_parser = ACSLParser(token_stream)
            tree = acsl_parser.acsl()
            if self.judger.visitAcsl(tree).type == ACSLType.ASSERTION:
                new_node = ACSLNode(
                    self.cur_acsl_order,
                    type=ACSLType.ASSERTION,
                    acsl=node.text.decode("utf-8"),
                )
                self.cur_parent.add_child(new_node)
            elif self.judger.visitAcsl(tree).type == ACSLType.LOOP:
                new_node = ACSLNode(
                    self.cur_acsl_order,
                    type=ACSLType.LOOP,
                    acsl=node.text.decode("utf-8"),
                )
                self.cur_parent.add_child(new_node)
                next_sibling = node.next_named_sibling
                body_node = self.find_first_body_node(next_sibling)
                if body_node:
                    self.cur_parent = new_node
                    self.traverse_acsl_annotations(body_node)
                self.cur_parent = new_node.parent
                self.next_sibling_is_visited = True
            elif self.judger.visitAcsl(tree).type == ACSLType.CONTRACT:
                new_node = ACSLNode(
                    self.cur_acsl_order,
                    type=ACSLType.CONTRACT,
                    acsl=node.text.decode("utf-8"),
                )
                self.cur_parent.add_child(new_node)
                next_sibling = node.next_named_sibling
                body_node = self.find_first_body_node(next_sibling)
                if body_node:
                    self.cur_parent = new_node
                    self.traverse_acsl_annotations(body_node)
                self.cur_parent = new_node.parent
                self.next_sibling_is_visited = True
            elif self.judger.visitAcsl(tree).type == ACSLType.LOGICDEF:
                new_node = ACSLNode(
                    self.cur_acsl_order,
                    type=ACSLType.LOGICDEF,
                    acsl=node.text.decode("utf-8"),
                )
                self.cur_parent.add_child(new_node)
            else:
                # meet unsupported ACSL Type, here is GhostCode!
                pass

        elif node.type == "function_definition":
            if self.next_sibling_is_visited:
                self.next_sibling_is_visited = False
                return
        elif (
            node.type == "for_statement"
            or node.type == "while_statement"
            or node.type == "do_statement"
        ):
            if self.next_sibling_is_visited:
                self.next_sibling_is_visited = False
                return

        for child in node.children:
            self.traverse_acsl_annotations(child)

    def build(self, code):
        code = self.remove_non_acsl_comments(code)
        tree = self.parser.parse(code.encode("utf-8"))
        node = tree.root_node
        self.traverse_acsl_annotations(node)

    def reverse_post_order_traversal(self):
        """
        Reverse Post-order
        """
        result = []

        def dfs(n):
            for child in reversed(n.children):
                dfs(child)
            result.append(n.name)

        dfs(self.root)
        return result[:-1]

    def print_tree(self, node=None, indent=0):
        if node is None:
            node = self.root
        print("  " * indent + f"Node(name={node.name}, type={node.type})")
        print("  " * indent + f"Annotation={node.acsl}")
        for child in node.children:
            self.print_tree(child, indent + 1)


if __name__ == "__main__":
    pass
