import ast
import _ast
import pysmt.shortcuts as shortcuts
#from lightdp.typing import Type

dot_operation_map = {
    ast.Eq: shortcuts.Equals,
    ast.Not: shortcuts.Not,
    ast.Gt: shortcuts.GT,
    ast.Lt: shortcuts.LT,
    ast.LtE: shortcuts.LE,
    ast.GtE: shortcuts.GE
}

oplus_operation_map = {
    ast.Add: shortcuts.Plus,
    ast.Sub: shortcuts.Minus
}

otimes_operation_map = {
    ast.Mult: shortcuts.Times,
    ast.Div: shortcuts.Div
}


class NodeVerifier(ast.NodeVisitor):
    def __init__(self):
        self.__environments = []

    @staticmethod
    def parse_docstring(s):
        assert s is not None
        from lightdp.lexer import build_lexer
        from lightdp.parser import build_parser
        lexer = build_lexer()
        parser = build_parser()
        return parser.parse(s, lexer=lexer)

    def visit_FunctionDef(self, node):
        annotation = NodeVerifier.parse_docstring(ast.get_docstring(node))
        if annotation is not None:
            self.__environments.append(annotation)
            super(NodeVerifier, self).generic_visit(node)
            self.__environments.pop()

    def visit_Assign(self, node):
        for target in node.targets:
            if target.id in self.__environments[len(self.__environments) - 1][1]:
                print(type(node.value))


def verify(tree):
    assert isinstance(tree, _ast.AST)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            verifier = NodeVerifier()
            verifier.visit(node)
            # TODO: do type inference here
