def build_parser():
    """
    Build a ply.parser for parsing LightDP
    :return: ply parser
    """
    import lightdp.ast as ast
    import ply.yacc as yacc

    from lightdp.lexer import tokens

    precedence = (
        ('left', 'LIST_TYPE', 'NUM_TYPE', 'BOOL_TYPE', 'TO'),
    )

    def p_annotation(p):
        """annotation : PRECONDITION EXPRESSION ';' type_declarations"""
        p[0] = (p[2], p[4])

    def p_type_declarations(p):
        """type_declarations : type_declarations ';' type_declaration
                             | type_declaration"""
        # merge the type_map
        type_map = {} if len(p) == 2 else p[1]
        declaration = p[1] if len(p) == 2 else p[3]

        for var in declaration[0]:
            type_map[var] = declaration[1]
        p[0] = type_map

    def p_type_declaration(p):
        """type_declaration : var_list ':' type"""
        p[0] = (p[1], p[3])

    def p_var_list(p):
        """var_list : var_list ',' IDENTIFIER
                    | IDENTIFIER"""
        if isinstance(p[1], list):
            p[1].append(p[3])
            p[0] = p[1]
        else:
            p[0] = [p[1]]

    def p_type(p):
        """type : NUM_TYPE EXPRESSION
                | NUM_TYPE '*'
                | BOOL_TYPE
                | LIST_TYPE type
                | type TO type"""

        if len(p) == 2:
            p[0] = ast.Type(p[1], None)
        elif len(p) == 3:
            p[0] = ast.Type(p[1], p[2])
        elif len(p) == 4:
            p[0] = ast.Type(p[1], p[2])

    def p_error(p):
        print('Error at %s' % p)

    return yacc.yacc(start='annotation')


