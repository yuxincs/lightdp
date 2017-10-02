reserved = {
        'if': 'IF',
        'then': 'THEN',
        'end': 'END',
        'else': 'ELSE',
        'true': 'BOOLEAN',
        'false': 'BOOLEAN',
        'num': 'NUM_TYPE',
        'bool': 'BOOL_TYPE',
        'list': 'LIST_TYPE',
        'return': 'RETURN',
        'skip': 'SKIP',
        'while': 'WHILE',
        'function': 'FUNCTION'
    }

tokens = ['REAL', 'ASSIGN', 'INDUCE', 'IDENTIFIER', 'LE', 'GE'] + list(set(reserved.values()))


def build_lexer():
    """
    Build a ply.lexer for scanning the token stream.
    :return: ply.lexer
    """
    import ply.lex as lex

    literals = "+-*/<>=(),:;[]{}!"
    t_ignore_COMMENT = r'\#.*'
    t_ignore_SPACE = r'\s'
    t_ASSIGN = ':='
    t_INDUCE = '->'
    t_GE = '>='
    t_LE = '<='

    def t_REAL(t):
        """([1-9]\d*|0)(\.\d+)?"""
        t.value = float(t.value)
        return t

    def t_IDENTIFIER(t):
        """[_a-zA-Z]([0-9]|[a-zA-Z]|_)*"""
        t.type = reserved.get(t.value, 'IDENTIFIER')
        return t

    def t_newline(t):
        r"""\n+"""
        t.lexer.lineno += len(t.value)

    def t_error(t):
        print("Error at line %d: Illegal character '%s'" % (t.lineno, t.value[0]))
        raise SyntaxError(t)

    return lex.lex()
