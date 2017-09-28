import ply.lex as lex
#lexer = lex.lex()


class Scanner:
    """ Package the implementation of Scanner
    """
    def __init__(self):
        pass

    def __iter__(self):
        return lexer.__iter__()

    def scan(self, s):
        pass
        #print(s)
        # lexer.input(s)

