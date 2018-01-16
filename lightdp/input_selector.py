import ast
import z3
from lightdp.typing import *
from .verifier import NodeVerifier


class CounterExampleGenerator(NodeVerifier):
    def __init__(self, args):
        super(CounterExampleGenerator, self).__init__()
        assert isinstance(args, dict)
        self._args = args
        self._db_var = None

    def visit_FunctionDef(self, node):
        self._db_var = node.args.args[-1].arg
        annotation = NodeVerifier.parse_docstring(ast.get_docstring(node))
        if annotation is not None:
            forall_vars, precondition, self._type_map = annotation

            # change the db_var's type
            self._type_map[self._db_var] = NumType('*')

            # set the distance vars for the corresponding normal vars
            from collections import OrderedDict
            for name, var_type in OrderedDict(self._type_map).items():
                constraint = None
                if isinstance(var_type, NumType):
                    self._type_map['^' + name] = NumType(0)
                    if var_type.value != '*':
                        constraint = self._symbol('^' + name) == self.visit(self.parse_expr(var_type.value))[0]
                elif isinstance(var_type, BoolType):
                    self._type_map['^' + name] = NumType(0)
                    constraint = self._symbol('^' + name) == 0
                elif isinstance(var_type, FunctionType):
                    # TODO: consider FunctionType
                    pass
                elif isinstance(var_type, ListType):
                    # TODO: consider list inside list
                    self._type_map['^' + name] = ListType(NumType(0))
                    symbol_i = self._symbol('i')
                    if isinstance(var_type.elem_type, NumType) and var_type.elem_type.value != '*':
                        constraint = self._symbol('^' + name)[symbol_i] == 0
                    elif isinstance(var_type.elem_type, BoolType):
                        constraint = self._symbol('^' + name)[symbol_i] == 0
                if constraint is not None:
                    self._declarations.append(constraint)

            # parse the precondition to constraint
            import re
            distance_vars = re.findall(r"""\^([_a-zA-Z][0-9a-zA-Z_]*)""", precondition)

            pre_constraint = self.visit(self.parse_expr(precondition.replace('^', '').replace(self._db_var + '[i]', self._db_var)))[0]
            for distance_var in distance_vars:
                pre_constraint = z3.substitute(pre_constraint,
                                               (self._symbol(distance_var), self._symbol('^' + distance_var)))

            self._precondition.append(pre_constraint)

            # empty the check list
            del self._if_checks[:]

            self.generic_visit(node)

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Call) and node.value.func.id == 'Laplace':
            self._declarations.append(self._symbol(node.targets[0].id) == 0)
        super(CounterExampleGenerator, self).visit_Assign(node)

    def get_constraint(self):
        for k, v in self._args.items():
            self._declarations.append(self._symbol(k) == v)
        final_constraint = z3.And(z3.And(self._precondition), z3.And(self._declarations), z3.And(self._assign_checks))
        return final_constraint, self._if_checks, self._symbol(self._db_var), self._symbol('^' + self._db_var)

    def visit_Subscript(self, node):
        # substitute the list-typed db_var with a single variable
        if node.value.id == self._db_var:
            return (self.visit(node.value)[0],
                    self.visit(node.value)[1])
        else:
            return super(CounterExampleGenerator, self).visit_Subscript(node)


def generate_inputs(tree, check_array):
    import _ast
    assert isinstance(tree, _ast.AST)
    generator = CounterExampleGenerator({'T': 10})
    generator.visit(tree)
    constraint, checks, db_var, db_distance_var = generator.get_constraint()

    d1 = []
    d2 = []
    s = z3.Solver()

    for i in range(len(check_array)):
        s.push()
        s.add(z3.And(constraint, z3.And(checks) if check_array[i] else z3.Not(z3.And(checks))))
        if s.check() == z3.sat:
            d1.append(float(s.model()[db_var].as_decimal(5)))
            d2.append(float(s.model()[db_var].as_decimal(5)) + float(s.model()[db_distance_var].as_decimal(5)))
            s.pop()
            s.add(z3.Or(db_var != s.model()[db_var], db_distance_var != s.model()[db_distance_var]))
        else:
            print('not sat')
            s.pop()

    return d1, d2

