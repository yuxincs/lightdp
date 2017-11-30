import ast
import _ast
import re
from lightdp.typing import *
import z3

_cmpop_map = {
    ast.Eq: lambda x, y: x == y,
    ast.Not: lambda x: z3.Not(x),
    ast.Gt: lambda x, y: x > y,
    ast.Lt: lambda x, y: x < y,
    ast.LtE: lambda x, y: x <= y,
    ast.GtE: lambda x, y: x >= y
}

_binop_map = {
    ast.Add: lambda x, y: x + y,
    ast.Sub: lambda x, y: x - y,
    ast.Mult: lambda x, y: x * y,
    ast.Div: lambda x, y: x / y
}

_boolop_map = {
    ast.And: lambda x, y: z3.And(x, y),
    ast.Or: lambda x, y: z3.Or(x, y)
}

_unop_map = {
    ast.USub: lambda x: -x
}


def _symbol(name, lightdp_type):
    if isinstance(lightdp_type, NumType):
        return z3.Real(name)
    elif isinstance(lightdp_type, ListType):
        if isinstance(lightdp_type.elem_type, NumType):
            return z3.Array(name, z3.RealSort(), z3.RealSort())
        elif isinstance(lightdp_type.elem_type, BoolType):
            return z3.Array(name, z3.BoolSort(), z3.RealSort())
        else:
            raise ValueError('Unsupported list inside list.')
    elif isinstance(lightdp_type, FunctionType):
        raise NotImplementedError('Function type is currently not supported.')
    elif isinstance(lightdp_type, BoolType):
        return z3.Bool(name)
    else:
        assert False, 'No such type %s' % lightdp_type


# translate the expression ast into pysmt constraints
class ExpressionTranslator(ast.NodeVisitor):
    def __init__(self, type_map, distance_vars=set()):
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
        return _cmpop_map[node.ops[0].__class__](self.visit(node.left), self.visit(node.comparators[0]))

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
        return _binop_map[node.op.__class__](self.visit(node.left), self.visit(node.right))

    def visit_Subscript(self, node):
        assert isinstance(node.slice, ast.Index), "Only index is supported."
        return shortcuts.Select(self.visit(node.value), self.visit(node.slice.value))

    def visit_BoolOp(self, node):
        from functools import reduce
        return reduce(_boolop_map[node.op.__class__], [self.visit(value) for value in node.values])

    def visit_UnaryOp(self, node):
        assert isinstance(node.op, tuple(_unop_map.keys()))
        return _unop_map[node.op.__class__](self.visit(node.operand))

    def generic_visit(self, node):
        assert False, 'Unexpeted node %s' % ast.dump(node)


class NodeVerifier(ast.NodeVisitor):
    def __init__(self, constraints):
        assert isinstance(constraints, list)
        self.__constraints = constraints
        self.__type_map = {}

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
            forall_vars, precondition, self.__type_map = annotation
            res = re.findall(r"""\^([_a-zA-Z][0-9a-zA-Z_]*)""", precondition)

            if forall_vars is None:
                self.__constraints.append(ExpressionTranslator(self.__type_map, set(res)).visit(ast.parse(precondition.replace('^', ''))))
            else:
                self.__constraints.append(
                    shortcuts.ForAll([shortcuts.Symbol(var, shortcuts.REAL) for var in forall_vars], ExpressionTranslator(self.__type_map, set(res)).visit(ast.parse(precondition.replace('^', '')))))

            for name, var_type in dict(self.__type_map).items():
                if name[0] == '^':
                    continue
                constraint = None
                if isinstance(var_type, NumType):
                    self.__type_map['^' + name] = NumType(0)
                    constraint = shortcuts.Equals(
                        shortcuts.Symbol('^' + name, to_smt_type(NumType(0))),
                        ExpressionTranslator(self.__type_map).visit(ast.parse(var_type.value)))
                elif isinstance(var_type, BoolType):
                    self.__type_map['^' + name] = NumType(0)
                    constraint = shortcuts.Equals(
                        shortcuts.Symbol('^' + name, to_smt_type(NumType(0))),
                        ExpressionTranslator(self.__type_map).visit(ast.parse('0')))
                elif isinstance(var_type, FunctionType):
                    # TODO: consider FunctionType
                    pass
                elif isinstance(var_type, ListType):
                    # TODO: consider list inside list
                    self.__type_map['^' + name] = ListType(NumType(0))
                    if isinstance(var_type.elem_type, NumType) and var_type.elem_type.value != '*':
                        symbol_i = shortcuts.Symbol('i', shortcuts.REAL)
                        constraint = shortcuts.ForAll([symbol_i],
                                                      shortcuts.Equals(
                            shortcuts.Select(shortcuts.Symbol('^' + name, to_smt_type(ListType(NumType(0)))), symbol_i),
                            ExpressionTranslator(self.__type_map).visit(ast.parse(var_type.elem_type.value))))
                    elif isinstance(var_type.elem_type, BoolType):
                        symbol_i = shortcuts.Symbol('i', shortcuts.REAL)
                        constraint = shortcuts.ForAll([symbol_i], shortcuts.Equals(
                            shortcuts.Select(shortcuts.Symbol('^' + name, to_smt_type(ListType(NumType(0)))), symbol_i),
                            ExpressionTranslator(self.__type_map).visit(ast.parse('0'))))
                if constraint is not None:
                    self.__constraints.append(constraint)
            self.generic_visit(node)

    def visit_If(self, node):
        self.__constraints.append(shortcuts.Equals(self.visit(node.test)[0], self.visit(node.test)[1]))
        self.generic_visit(node)

    def visit_Compare(self, node):
        assert len(node.ops) == 1 and len(node.comparators), "Only allow one comparators in binary operations."
        left_expr = self.visit(node.left)
        right_expr = self.visit(node.comparators[0])
        return (_cmpop_map[node.ops[0].__class__](left_expr[0], right_expr[0]),
                _cmpop_map[node.ops[0].__class__](left_expr[0] + left_expr[1], right_expr[0] + right_expr[1]))

    def visit_Name(self, node):
        assert node.id in self.__type_map, 'Undefined %s' % node.id
        return (shortcuts.Symbol(node.id, to_smt_type(self.__type_map[node.id])),
                shortcuts.Symbol('^' + node.id, to_smt_type(self.__type_map['^' + node.id])))

    def visit_Num(self, node):
        return shortcuts.Real(node.n), shortcuts.Real(0)

    def visit_BinOp(self, node):
        assert isinstance(node.op, tuple(_binop_map.keys())), 'Unsupported BinOp %s' % ast.dump(node.op)
        return (_binop_map[node.op.__class__](self.visit(node.left)[0], self.visit(node.right)[0]),
                _binop_map[node.op.__class__](self.visit(node.left)[1], self.visit(node.right)[1]))

    def visit_Subscript(self, node):
        assert isinstance(node.slice, ast.Index), "Only index is supported."
        return (shortcuts.Select(self.visit(node.value)[0], self.visit(node.slice.value)[0]),
                shortcuts.Select(self.visit(node.value)[1], self.visit(node.slice.value)[0]))

    def visit_BoolOp(self, node):
        assert isinstance(node.op, tuple(_boolop_map.keys())), 'Unsupported BoolOp %s' % ast.dump(node.op)
        from functools import reduce
        return (reduce(_boolop_map[node.op.__class__], [self.visit(value)[0] for value in node.values]),
                reduce(_boolop_map[node.op.__class__], [self.visit(value)[1] for value in node.values]))

    def visit_UnaryOp(self, node):
        assert isinstance(node.op, tuple(_unop_map.keys())), 'Unsupported UnaryOp %s' % ast.dump(node.op)
        return (_unop_map[node.op.__class__](self.visit(node.operand)[0]),
                _unop_map[node.op.__class__](self.visit(node.operand)[1]))

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Call) and node.value.func.id == 'Laplace':
            pass
        elif len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            target_type = self.__type_map[node.targets[0].id]
            if isinstance(target_type, ListType):
                # TODO: list assignment
                pass
            else:
                self.__constraints.append(shortcuts.Equals(self.visit(node.targets[0])[1], self.visit(node.value)[1]))
        else:
            assert False, 'Currently don\'t support multiple assignment.'

    def visit_NameConstant(self, node):
        assert node.value == True or node.value == False, 'Unsupported NameConstant %s' % str(node.value)
        return node.value, NumType(0)

    def visit_Call(self, node):
        if isinstance(node.func, ast.Attribute) and node.func.attr == 'append':
            # type check
            assert isinstance(self.__type_map[node.func.value.id], ListType), \
                '%s is not typed as list.' % node.func.value.id
            if isinstance(self.__type_map[node.func.value.id].elem_type, NumType):
                self.__constraints.append(shortcuts.Equals(shortcuts.Select(self.visit(node.func.value.id)[1], self.visit(ast.Name('i'))), self.visit(node.args[0])[1]))

        else:
            # TODO: check the function return type.
            pass


def verify(tree):
    assert isinstance(tree, _ast.AST)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            # TODO: consider multiple functions scenario
            constraints = []
            NodeVerifier(constraints).visit(node)
            final_constraints = z3.And(constraints[0], z3.Not(z3.And(constraints[1:])))

            print('\033[32;1mPrecondition:\033[0m')
            print(constraints[0])
            print('\033[32;1mConstraints:\033[0m')
            for constraint in constraints[1:]:
                print(constraint)
            print('\033[32;1mFinal Constraint:\033[0m')
            print(final_constraints)

            s = z3.Solver()
            s.add(final_constraints)
            return s.check()
