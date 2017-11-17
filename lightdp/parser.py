def build_parser():
    """
    Build a ply.parser for parsing LightDP
    :return: ply parser
    """
    from lightdp.typing import NumType, ListType, BoolType, FunctionType
    import ply.yacc as yacc

    from lightdp.lexer import tokens

    precedence = (
        ('left', 'LIST_TYPE', 'NUM_TYPE', 'BOOL_TYPE', 'TO'),
    )

    def p_annotation(p):
        r"""annotation : PRECONDITION EXPRESSION ';' type_declarations"""
        p[0] = (p[2], p[4])

    def p_type_declarations(p):
        r"""type_declarations : type_declarations ';' type_declaration
                             | type_declaration"""
        declaration = p[1] if len(p) == 2 else p[3]

        for var in declaration[0]:
            p.parser.type_map[var] = declaration[1]

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
                p[0] = NumType(p[2])
        elif len(p) == 4:
            p[0] = FunctionType(p[1], p[2])

    def p_error(p):
        print('Error at %s' % p)

    parser = yacc.yacc(start='annotation')
    parser.type_map = {}
    return parser
