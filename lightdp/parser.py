def build_parser():
    """
    Build a ply.parser for parsing LightDP
    :return: ply parser
    """
    from lightdp.typing import NumType, ListType, BoolType, FunctionType, to_smt_type
    from lightdp.verifier import dot_operation_map, oplus_operation_map, otimes_operation_map
    import pysmt.shortcuts as shortcuts
    import ply.yacc as yacc
    import ast

    class ExpressionParser(ast.NodeVisitor):
        def __init__(self, type_map):
            self.type_map = type_map

        def visit_Module(self, node):
            assert isinstance(node.body[0], ast.Expr)
            super(ExpressionParser, self).generic_visit(node.body[0])

        def visit_IfExp(self, node):
            return shortcuts.Ite(self.visit(node.test), self.visit(node.body), self.visit(node.orelse))

        def visit_Compare(self, node):
            assert len(node.ops) == 1 and len(node.comparators), "Only allow one comparators in binary operations."
            return dot_operation_map[node.ops[0].__class__](self.visit(node.left), self.visit(node.comparators[0]))

        def visit_Name(self, node):
            assert node.id in self.type_map, "%s not defined." % node.id
            return self.type_map[node.id][0]

        def visit_Num(self, node):
            return shortcuts.Int(node.n) if isinstance(node.n, int) else shortcuts.Real(node.n)

        def visit_BinOp(self, node):
            if isinstance(node.op, tuple(oplus_operation_map.keys())):
                return oplus_operation_map[node.op.__class__](self.visit(node.left), self.visit(node.right))
            elif isinstance(node.op, tuple(otimes_operation_map.keys())):
                return otimes_operation_map[node.op.__class__](self.visit(node.left), self.visit(node.right))

        def visit_Subscript(self, node):
            assert isinstance(node.slice, ast.Index), "Only index is supported."
            shortcuts.Select(self.visit(node.value), self.visit(node.slice.value))

        def generic_visit(self, node):
            assert False, 'Unexpeted node %s' % ast.dump(node)

    from lightdp.lexer import tokens

    precedence = (
        ('left', 'LIST_TYPE', 'NUM_TYPE', 'BOOL_TYPE', 'TO'),
    )

    def p_annotation(p):
        r"""annotation : PRECONDITION EXPRESSION ';' type_declarations"""
        p[0] = (ast.parse(p[2]), p[4])

    def p_type_declarations(p):
        r"""type_declarations : type_declarations ';' type_declaration
                             | type_declaration"""
        declaration = p[1] if len(p) == 2 else p[3]

        for var in declaration[0]:
            p.parser.type_map[var] = (shortcuts.Symbol(var, to_smt_type(declaration[1])), declaration[1])
        p[0] = p.parser.type_map

    def p_type_declaration(p):
        r"""type_declaration : var_list ':' type"""
        p[0] = (p[1], p[3])

    def p_var_list(p):
        r"""var_list : var_list ',' IDENTIFIER
                    | IDENTIFIER"""
        if isinstance(p[1], list):
            p[1].append(p[3])
            p[0] = p[1]
        else:
            p[0] = [p[1]]

    def p_type(p):
        r"""type : BOOL_TYPE
                | NUM_TYPE EXPRESSION
                | NUM_TYPE '*'
                | LIST_TYPE type
                | type TO type"""

        if len(p) == 2:
            p[0] = BoolType()
        elif len(p) == 3:
            if isinstance(p[2], (ListType, NumType, FunctionType, BoolType)):
                p[0] = ListType(p[2])
            elif p[2] == '*':
                p[0] = NumType('*')
            else:
                p[0] = NumType(ExpressionParser(p.parser.type_map).visit(ast.parse(p[2])))
        elif len(p) == 4:
            p[0] = FunctionType(p[1], p[2])

    def p_error(p):
        print('Error at %s' % p)

    parser = yacc.yacc(start='annotation')
    parser.type_map = {}
    return parser
