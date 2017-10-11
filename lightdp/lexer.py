reserved = {
        'if': 'IF',
        'else': 'ELSE',
        'true': 'BOOLEAN',
        'false': 'BOOLEAN',
        'num': 'NUM_TYPE',
        'bool': 'BOOL_TYPE',
        'list': 'LIST_TYPE',
        'returns': 'RETURNS',
        'skip': 'SKIP',
        'while': 'WHILE',
        'function': 'FUNCTION',
        'and': 'AND',
        'or': 'OR'
    }

tokens = ['REAL', 'ASSIGN', 'INDUCE', 'IDENTIFIER', 'LE', 'GE', 'CONS'] + list(set(reserved.values()))


def build_lexer():
    """
    Build a ply.lexer for scanning the token stream.
    :return: ply.lexer
    """
    import ply.lex as lex

    literals = "+-*/<>=(),:;[]{}!?"
    t_ignore_COMMENT = r'\#.*'
    t_ignore_SPACE = r'\s'
    t_ASSIGN = ':='
    t_INDUCE = '->'
    t_GE = '>='
    t_LE = '<='
    t_CONS = '::'

    def t_REAL(t):
        """([1-9]\d*|0)(\.\d+)?"""
        if '.' in t.value:
            t.value = float(t.value)
        else:
            t.value = int(t.value)
        return t

    def t_IDENTIFIER(t):
        """[_a-zA-Z]([0-9]|[a-zA-Z]|_)*"""
        t.type = reserved.get(t.value, 'IDENTIFIER')
        if t.type == 'BOOLEAN':
            t.value = True if t.value == 'true' else False
        return t

    def t_newline(t):
        r"""\n+"""
        t.lexer.lineno += len(t.value)

    def t_error(t):
        print("Error at line %d: Illegal character '%s'" % (t.lineno, t.value[0]))
        raise SyntaxError(t)

    return lex.lex()
