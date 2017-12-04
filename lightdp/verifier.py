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


class NodeVerifier(ast.NodeVisitor):
    def __init__(self, constraints):
        assert isinstance(constraints, dict)
        self.__precondition = constraints['precondition']
        self.__declarations = constraints['declarations']
        self.__checks = constraints['checks']
        self.__type_map = None

    def __symbol(self, name):
        lightdp_type = self.__type_map[name]
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

    @staticmethod
    def parse_docstring(s):
        assert s is not None
        from lightdp.lexer import build_lexer
        from lightdp.parser import build_parser
        lexer = build_lexer()
        parser = build_parser()
        return parser.parse(s, lexer=lexer)

    @staticmethod
    def parse_expr(expr):
        node = ast.parse(expr)
        assert isinstance(node, ast.Module) and isinstance(node.body[0], ast.Expr), \
            r"""expr_parse fed with illegal expression string '%s'""" % expr
        return node.body[0].value

    def visit_FunctionDef(self, node):
        annotation = NodeVerifier.parse_docstring(ast.get_docstring(node))
        if annotation is not None:
            forall_vars, precondition, self.__type_map = annotation

            # set the distance vars for the corresponding normal vars
            from collections import OrderedDict
            for name, var_type in OrderedDict(self.__type_map).items():
                constraint = None
                if isinstance(var_type, NumType):
                    self.__type_map['^' + name] = NumType(0)
                    constraint = self.__symbol('^' + name) == \
                                 self.visit(self.parse_expr(var_type.value))[0]
                elif isinstance(var_type, BoolType):
                    self.__type_map['^' + name] = NumType(0)
                    constraint = self.__symbol('^' + name) == \
                                 self.visit(self.parse_expr('0'))[0]
                elif isinstance(var_type, FunctionType):
                    # TODO: consider FunctionType
                    pass
                elif isinstance(var_type, ListType):
                    # TODO: consider list inside list
                    self.__type_map['^' + name] = ListType(NumType(0))
                    symbol_i = self.__symbol('i')
                    if isinstance(var_type.elem_type, NumType) and var_type.elem_type.value != '*':
                        constraint = self.__symbol('^' + name)[symbol_i] == \
                                     self.visit(self.parse_expr(var_type.elem_type.value))[0]
                    elif isinstance(var_type.elem_type, BoolType):
                        constraint = self.__symbol('^' + name)[symbol_i] == \
                                     self.visit(self.parse_expr('0'))[0]
                if constraint is not None:
                    self.__constraints.append(constraint)

            # parse the precondition to constraint
            distance_vars = re.findall(r"""\^([_a-zA-Z][0-9a-zA-Z_]*)""", precondition)

            pre_constraint = self.visit(self.parse_expr(precondition.replace('^', '')))[0]
            for distance_var in distance_vars:
                pre_constraint = z3.substitute(pre_constraint,
                                               (self.__symbol(distance_var), self.__symbol('^' + distance_var)))

            if forall_vars is not None:
                pre_constraint = z3.ForAll([self.__symbol(var) for var in forall_vars], pre_constraint)

            self.__constraints.insert(0, pre_constraint)
            self.__precondition = [pre_constraint]

            # empty the check list
            self.__checks = []

            self.generic_visit(node)

    def visit_If(self, node):
        test_node = self.visit(node.test)
        self.__constraints.append(test_node[0] == test_node[1])
        self.generic_visit(node)

    def visit_IfExp(self, node):
        test_node = self.visit(node.test)
        self.__constraints.append(test_node[0] == test_node[1])
        return z3.If(test_node[0], self.visit(node.body)[0], self.visit(node.orelse)[0]), \
               z3.If(test_node[1], self.visit(node.body)[1], self.visit(node.orelse)[1])

    def visit_Compare(self, node):
        assert len(node.ops) == 1 and len(node.comparators), 'Only allow one comparators in binary operations.'
        left_expr = self.visit(node.left)
        right_expr = self.visit(node.comparators[0])
        return (_cmpop_map[node.ops[0].__class__](left_expr[0], right_expr[0]),
                _cmpop_map[node.ops[0].__class__](left_expr[0] + left_expr[1], right_expr[0] + right_expr[1]))

    def visit_Name(self, node):
        assert node.id in self.__type_map, 'Undefined %s' % node.id
        return self.__symbol(node.id), self.__symbol('^' + node.id)

    def visit_Num(self, node):
        return node.n, 0

    def visit_BinOp(self, node):
        assert isinstance(node.op, tuple(_binop_map.keys())), 'Unsupported BinOp %s' % ast.dump(node.op)
        return (_binop_map[node.op.__class__](self.visit(node.left)[0], self.visit(node.right)[0]),
                _binop_map[node.op.__class__](self.visit(node.left)[1], self.visit(node.right)[1]))

    def visit_Subscript(self, node):
        assert isinstance(node.slice, ast.Index), 'Only index is supported.'
        return (self.visit(node.value)[0][self.visit(node.slice.value)[0]],
                self.visit(node.value)[1][self.visit(node.slice.value)[0]])

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
                # raise NotImplementedError('List assignment not implemented.')
            else:
                self.__constraints.append(self.visit(node.targets[0])[1] == self.visit(node.value)[1])
        else:
            raise NotImplementedError('Currently don\'t support multiple assignment.')

    def visit_NameConstant(self, node):
        assert node.value is True or node.value is False, 'Unsupported NameConstant %s' % str(node.value)
        return node.value, NumType(0)

    def visit_Call(self, node):
        if isinstance(node.func, ast.Attribute) and node.func.attr == 'append':
            # type check
            assert isinstance(self.__type_map[node.func.value.id], ListType), \
                '%s is not typed as list.' % node.func.value.id
            if isinstance(self.__type_map[node.func.value.id].elem_type, NumType):
                self.__constraints.append(self.visit(node.func.value.id)[1][self.__symbol('i')] ==
                                          self.visit(node.args[0])[1])

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
