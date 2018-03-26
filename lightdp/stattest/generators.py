import ast
import z3
from lightdp.typing import *
from lightdp.verifier import NodeVerifier


class _SymbolicInputGenerator(NodeVerifier):
    def __init__(self, args):
        super(_SymbolicInputGenerator, self).__init__()
        assert isinstance(args, dict)
        self._args = args
        self._db_var = None
        self._if_not_checks = []
        self._dependent_loop_vars = []

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
                        constraint = self._symbol('^' + name) == 0
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
            del self._if_not_checks[:]

            self.generic_visit(node)

    def visit_While(self, node):
        if isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Str):
            self._dependent_loop_vars.extend(node.body[0].value.s.split(','))
        self.generic_visit(node)

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Call) and node.value.func.id == 'Laplace':
            self._declarations.append(self._symbol(node.targets[0].id) == 0)
        elif len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            target_type = self._type_map[node.targets[0].id]
            if isinstance(target_type, ListType):
                # TODO: list assignment
                pass
                # raise NotImplementedError('List assignment not implemented.')
            else:
                for child in ast.iter_child_nodes(node.value):
                    if isinstance(child, ast.Name) and child.id in self._args.keys():
                        self._declarations.append(self.visit(node.targets[0])[0] == self.visit(node.value)[0])
                        break
        else:
            raise NotImplementedError('Currently don\'t support multiple assignment.')

    def get_constraint(self):
        for k, v in self._args.items():
            self._declarations.append(self._symbol(k) == v)
        final_constraint = z3.And(z3.And(self._precondition), z3.And(self._declarations), z3.And(self._assign_checks))
        return final_constraint, self._if_checks, self._if_not_checks, \
            self._symbol(self._db_var), self._symbol('^' + self._db_var), \
            [self._symbol(var) for var in self._dependent_loop_vars]

    def visit_Subscript(self, node):
        # substitute the list-typed db_var with a single variable
        if node.value.id == self._db_var:
            return (self.visit(node.value)[0],
                    self.visit(node.value)[1])
        else:
            return super(_SymbolicInputGenerator, self).visit_Subscript(node)

    def visit_If(self, node):
        test_node = self.visit(node.test)
        self._if_checks.append(test_node[0] == test_node[1])
        self._if_not_checks.append(test_node[0] != test_node[1])
        self.generic_visit(node)

    def visit_IfExp(self, node):
        test_node = self.visit(node.test)
        self._if_checks.append(test_node[0] == test_node[1])
        self._if_not_checks.append(test_node[0] != test_node[1])
        return z3.If(test_node[0], self.visit(node.body)[0], self.visit(node.orelse)[0]), \
            z3.If(test_node[1], self.visit(node.body)[1], self.visit(node.orelse)[1])


def symbolic_generator(tree, args, num_input, fixed_d1=[]):
    """
    :param tree: The algorithm's AST tree
    :param args: The argument to be put in the algorithm
    :param num_input: The number of inputs to generate
    :param fixed_d1: Optional, will only generate database 2 according to the given database 1 if provided
    :return:
    """
    import _ast
    assert isinstance(tree, _ast.AST)
    assert len(fixed_d1) == 0 or num_input == len(fixed_d1), "num_input and len(fixed_d1) must match"

    generator = _SymbolicInputGenerator(args)
    generator.visit(tree)
    constraint, checks, not_checks, db_var, db_distance_var, loop_dependent_vars = generator.get_constraint()

    d1 = fixed_d1
    d2 = []
    s = z3.Solver()
    # TODO: think of a good way for control parameters
    check_array = [False for _ in range(num_input)]

    for i in range(len(d1)):
        s.add(z3.And(constraint))
        s.push()
        s.add(db_var == d1[i])
        s.add(db_distance_var != 0)
        s.add(z3.And(checks) if check_array[i] else z3.And(not_checks))
        try:
            for loop_dependent_var in loop_dependent_vars:
                s.add(loop_dependent_var == s.model()[loop_dependent_var])
        except z3.Z3Exception:
            pass
        if s.check() == z3.sat:
            d2.append(float(s.model()[db_var].as_decimal(5).replace('?', '')) +
                      float(s.model()[db_distance_var].as_decimal(5).replace('?', '')))
            s.pop()
            s.add(z3.Or(db_var != s.model()[db_var], db_distance_var != s.model()[db_distance_var]))
        else:
            assert False, 'Cannot satisfy the constraints'

    print(d1, d2)
    return d1, d2


# TODO: to remove manual search space in the future
def simple_generator(algorithm, args, kwargs, num_input, search_space):
    """
    :param algorithm: The algorithm to run.
    :param args: The argument for the algorithm.
    :param kwargs: The keyword argument for the algorithm.
    :param num_input: The number of inputs to be generated
    :return: Database (d1, d2)
    """
    assert isinstance(args, tuple)
    assert isinstance(kwargs, dict)
    from .core import hypothesis_test
    from .selectors import fisher_s_selector
    import numpy as np
    # assume maximum distance is 1
    d1 = [1 for _ in range(num_input)]
    candidates = [
        (d1, [0] + [1 for _ in range(num_input - 1)]),  # one below
        (d1, [2] + [1 for _ in range(num_input - 1)]),  # one above
        (d1, [2] + [0 for _ in range(num_input - 1)]),  # one above rest below
        (d1, [0] + [2 for _ in range(num_input - 1)]),  # one below rest above
        (d1, [2 for _ in range(int(num_input / 2))] + [0 for _ in range(num_input - int(num_input / 2))]),  # half half
        (d1, [2 for _ in range(num_input)]),  # all above
        (d1, [0 for _ in range(num_input)]),  # all below
    ]

    results = []

    for d1, d2 in candidates:
        candidate_result = []
        for algorithm_epsilon in [0.2, 0.5, 0.7, 1, 2, 3]:
            kwargs['eps'] = algorithm_epsilon

            rising_epsilon = 0.1
            steady_epsilon = algorithm_epsilon + 2.0
            previous_p = [0.0, 0.0]
            for test_epsilon in np.arange(max(algorithm_epsilon - 0.5, 0.1), algorithm_epsilon + 2.0, 0.1):
                s = fisher_s_selector(algorithm, args, kwargs, d1, d2, test_epsilon, search_space=search_space)
                p1, p2 = hypothesis_test(algorithm, args, kwargs, d1, d2, s, test_epsilon, iterations=100000, cores=0)

                rising_epsilon = test_epsilon if p1 < 0.05 and previous_p < [0.05, 0.05] else rising_epsilon

                steady_epsilon = test_epsilon if p1 > 0.95 and previous_p > [0.95, 0.95] else steady_epsilon

                # store the new p into the history
                previous_p[0], previous_p[1] = previous_p[1], previous_p[0]
                previous_p[0] = p1

                # stop early for best performance
                if steady_epsilon < algorithm_epsilon + 2.0:
                    break
            candidate_result.append(rising_epsilon / algorithm_epsilon + 1.0 / (steady_epsilon - rising_epsilon))
        results.append(np.mean(candidate_result))

    return candidates[np.argmax(results)]
