def build_parser():
    """
    Build a ply.parser for parsing LightDP
    :return: ply parser
    """
    import lightdp.ast as ast
    import ply.yacc as yacc

    from lightdp.lexer import tokens

    precedence = (
        ('left', '+', '-', '<', '>', '=', 'LE', 'GE'),
        ('left', '*', '/', ':'),
        ('left', '?', 'CONS', 'ASSIGN', 'INDUCE'),
        ('right', '!'),
        ('nonassoc', 'LOWER_THAN_ELSE'),
        ('nonassoc', 'ELSE')
    )

    def p_function(p):
        """function : function_declaration '{' statement_list '}'"""
        p[0] = ast.Function(p[1], p[3])

    def p_while(p):
        """while : WHILE '(' expression ')' statement
                 | WHILE '(' expression ')' '{' statement_list '}'"""
        if len(p) == 6:
            p[0] = ast.While(p[3], p[5])
        elif len(p) == 8:
            p[0] = ast.While(p[3], p[6])

    def p_if(p):
        """if : IF '(' expression ')' '{' statement_list '}' %prec LOWER_THAN_ELSE
              | IF '(' expression ')' statement %prec LOWER_THAN_ELSE"""
        if len(p) == 6:
            p[0] = ast.If(p[3], p[5], None)
        elif len(p) == 8:
            p[0] = ast.If(p[3], p[6], None)

    def p_if_with_else(p):
        """if : IF '(' expression ')' statement ELSE statement
              | IF '(' expression ')' statement ELSE '{' statement_list '}'"""
        if len(p) == 8:
            p[0] = ast.If(p[3], p[5], p[7])
        elif len(p) == 10:
            p[0] = ast.If(p[3], p[5], p[8])

    def p_if_with_else_and_list(p):
        """if : IF '(' expression ')' '{' statement_list '}' ELSE statement
              | IF '(' expression ')' '{' statement_list '}' ELSE '{' statement_list '}'"""
        if len(p) == 10:
            p[0] = ast.If(p[3], p[6], p[9])
        elif len(p) == 12:
            p[0] = ast.If(p[3], p[6], p[10])

    def p_statement_list(p):
        """statement_list : statement_list statement
                          | statement"""
        if len(p) == 2:
            p[0] = [p[1]]
        elif len(p) == 3:
            assert isinstance(p[1], list)
            p[1].append(p[2])
            p[0] = p[1]

    def p_statement(p):
        """statement : expression ';'
                     | assign ';'
                     | type_declarations
                     | if
                     | function
                     | while"""
        p[0] = p[1]

    def p_assign(p):
        """assign : IDENTIFIER ASSIGN expression"""
        p[0] = ast.Assign(p[1], p[3])

    def p_function_declaration(p):
        """function_declaration : FUNCTION IDENTIFIER '(' type_declarations ')' RETURNS '(' type_declarations ')'"""
        p[0] = ast.FunctionDeclaration(p[2], p[4], p[8])

    def p_type_declarations(p):
        """type_declarations : type_declarations ';' type_declaration
                             | type_declaration"""
        if len(p) == 2:
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[3]]

    def p_type_declaration(p):
        """type_declaration : var_list ':' type
                            | IDENTIFIER ':' type"""
        if isinstance(p[1], str):
            p[0] = ast.TypeDeclaration([ast.Variable(p[1])], p[3])
        else:
            p[0] = ast.TypeDeclaration(p[1], p[3])

    def p_arg_list(p):
        """var_list : IDENTIFIER ',' var_list
                    | IDENTIFIER ',' IDENTIFIER"""
        # cannot simply use IDENTIFIER on this which will cause reduce/reduce conlficts
        # with expression rule
        if isinstance(p[3], list):
            p[0] = [ast.Variable(p[1])] + p[3]
        else:
            p[0] = [ast.Variable(p[1]), ast.Variable(p[3])]

    def p_type(p):
        """type : NUM_TYPE '(' expression ')'
                | NUM_TYPE '(' '*' ')'
                | BOOL_TYPE
                | LIST_TYPE type
                | type INDUCE type"""
        if len(p) == 2:
            p[0] = ast.Type(p[1], None)
        elif len(p) == 5:
            p[0] = ast.Type(p[1], p[3])
        elif len(p) == 3:
            p[0] = ast.Type(p[1], p[2])
        elif len(p) == 4:
            p[0] = ast.Type(p[1], p[2])

    def p_expression_list(p):
        """expression_list : expression_list ',' expression
                           | expression"""
        if len(p) == 2:
            p[0] = [p[1]]
        elif len(p) == 4:
            assert isinstance(p[1], list)
            p[1].append(p[3])
            p[0] = p[1]

    def p_expression_variable(p):
        """expression : REAL
                      | BOOLEAN
                      | IDENTIFIER"""
        if isinstance(p[1], str):
            p[0] = ast.Variable(p[1])
        elif isinstance(p[1], float):
            p[0] = ast.Real(p[1])
        else:
            p[0] = ast.Boolean(p[1])

    def p_expression_unary(p):
        """expression : '!' expression"""
        p[0] = ast.UnaryOperation(p[1], p[2])

    def p_expression_binary(p):
        """expression : expression '+' expression
                      | expression '-' expression
                      | expression '*' expression
                      | expression '/' expression
                      | expression '<' expression
                      | expression '>' expression
                      | expression '=' expression
                      | expression LE expression
                      | expression GE expression
                      | expression CONS expression"""
        p[0] = ast.BinaryOperation(p[2], p[1], p[3])

    def p_expression_other(p):
        """expression : IDENTIFIER '[' expression ']'
                      | expression '?' expression ':' expression"""
        if len(p) == 5:
            p[0] = ast.ListIndex(p[1], p[3])
        elif len(p) == 6:
            p[0] = ast.ConditionalVariable(p[1], p[3], p[5])

    def p_expression_call(p):
        """expression : IDENTIFIER '(' ')'
                      | IDENTIFIER '(' expression_list ')'"""
        if len(p) == 4:
            p[0] = ast.FunctionCall(p[1], None)
        elif len(p) == 5:
            p[0] = ast.FunctionCall(p[1], p[3])

    def p_error(p):
        print('Error at %s' % p)

    return yacc.yacc(start='statement_list')


