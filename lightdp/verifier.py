import ast
import _ast
from pysmt.shortcuts import Symbol, GE, LE, LT, GT, Equals, Not
from lightdp.type import Type

_dot_operation_map = {
    ast.Eq: Equals,
    ast.Not: Not,
    ast.Gt: GT,
    ast.Lt: LT,
    ast.LtE: LE,
    ast.GtE: GE
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

    def visit_Num(self, node):
        return Type('num', ast.parse('0'))

    def visit_BinOp(self, node):
        if isinstance(node.op, _dot_operation_map.keys()):
            pass
        elif isinstance(node.op, ast.):
            pass
        #elif node.op


def verify(tree):
    assert isinstance(tree, _ast.AST)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            verifier = NodeVerifier()
            verifier.visit(node)
            # TODO: do type inference here
