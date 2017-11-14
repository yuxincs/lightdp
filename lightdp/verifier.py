import ast
import _ast
import pysmt.shortcuts as shortcuts
from lightdp.typing import *

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

bool_operation_map = {
    ast.And: shortcuts.And,
    ast.Or: shortcuts.Or
}

unary_operation_map = {
    ast.USub: lambda x: shortcuts.Minus(shortcuts.Real(0), x)
}


# translate the expression ast into pysmt constraints
class ExpressionTranslator(ast.NodeVisitor):
    def __init__(self, type_map, distance_vars = set()):
        self.type_map = type_map
        self.__distance_vars = distance_vars

    def visit_Module(self, node):
        assert isinstance(node.body[0], ast.Expr)
        return self.visit(node.body[0])

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_IfExp(self, node):
        return shortcuts.Ite(self.visit(node.test), self.visit(node.body), self.visit(node.orelse))

    def visit_Compare(self, node):
        assert len(node.ops) == 1 and len(node.comparators), "Only allow one comparators in binary operations."
        return dot_operation_map[node.ops[0].__class__](self.visit(node.left), self.visit(node.comparators[0]))

    def visit_Name(self, node):
        name = '^' + node.id if node.id in self.__distance_vars else node.id

        assert name[0] == '^' or name in self.type_map, 'Undefined %s' % name
        if name[0] == '^':
            if isinstance(self.type_map[name[1:]], (NumType, BoolType, FunctionType)):
                self.type_map[name] = NumType(0)
            elif isinstance(self.type_map[name[1:]], ListType):
                self.type_map[name] = ListType(NumType(0))

        return shortcuts.Symbol(name, to_smt_type(self.type_map[name]))

    def visit_Num(self, node):
        return shortcuts.Real(node.n)

    def visit_BinOp(self, node):
        if isinstance(node.op, tuple(oplus_operation_map.keys())):
            return oplus_operation_map[node.op.__class__](self.visit(node.left), self.visit(node.right))
        elif isinstance(node.op, tuple(otimes_operation_map.keys())):
            return otimes_operation_map[node.op.__class__](self.visit(node.left), self.visit(node.right))

    def visit_Subscript(self, node):
        assert isinstance(node.slice, ast.Index), "Only index is supported."
        return shortcuts.Select(self.visit(node.value), self.visit(node.slice.value))

    def visit_BoolOp(self, node):
        assert isinstance(node.op, tuple(bool_operation_map.keys()))
        return bool_operation_map[node.op.__class__]([self.visit(value) for value in node.values])

    def visit_UnaryOp(self, node):
        assert isinstance(node.op ,tuple(unary_operation_map.keys()))
        return unary_operation_map[node.op.__class__](self.visit(node.operand))

    def generic_visit(self, node):
        assert False, 'Unexpeted node %s' % ast.dump(node)


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
