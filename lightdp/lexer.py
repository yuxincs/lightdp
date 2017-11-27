reserved = {
        'num': 'NUM_TYPE',
        'bool': 'BOOL_TYPE',
        'list': 'LIST_TYPE',
        'precondition': 'PRECONDITION',
        'forall': 'FORALL'
    }

tokens = ['IDENTIFIER', 'EXPRESSION', 'TO'] + list(set(reserved.values()))


def build_lexer():
    """
    Build a ply.lexer for scanning the token stream.
    :return: ply.lexer
    """
    import ply.lex as lex

    literals = "();:*,"
    t_ignore_SPACE = r'\s'
    t_TO = '->'

    states = (
        ('expression', 'exclusive'),
    )

    def t_expression(t):
        r"""\("""
        t.lexer.expression_start = t.lexer.lexpos
        t.lexer.level = 1
        t.lexer.begin('expression')

    def t_expression_lbrace(t):
        r"""\("""
        t.lexer.level += 1

    def t_expression_rbrace(t):
        r"""\)"""
        t.lexer.level -= 1

        if t.lexer.level == 0:
            t.value = t.lexer.lexdata[t.lexer.expression_start:t.lexer.lexpos - 1]
            if t.value == '*':
                t.type = '*'
            else:
                t.type = 'EXPRESSION'
                t.lexer.lineno += t.value.count('\n')
                t.value.replace('\n', '')
            t.lexer.begin('INITIAL')
            return t

    def t_expression_content(t):
        r"""[^\(\)]"""
        pass

    def t_expression_error(t):
        t_error(t)

    def t_IDENTIFIER(t):
        r"""[\^_a-zA-Z]([0-9]|[a-zA-Z]|_)*"""
        t.type = reserved.get(t.value, 'IDENTIFIER')
        return t

    def t_newline(t):
        r"""\n+"""
        t.lexer.lineno += len(t.value)

    def t_error(t):
        print("Error at line %d: Illegal character '%s'" % (t.lineno, t.value[0]))
        raise SyntaxError(t)

    return lex.lex()
