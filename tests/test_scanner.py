import pytest
from lightdp.scanner import build_lexer


def test_function_declaration():
    lexer = build_lexer()
    lexer.input('function SparseVector(T, N, epsilon : num(0); q : list num(*))')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('FUNCTION', 'function'), ('IDENTIFIER', 'SparseVector'), ('(', '('),
                      ('IDENTIFIER', 'T'), (',', ','), ('IDENTIFIER', 'N'), (',', ','),
                      ('IDENTIFIER', 'epsilon'), (':', ':'), ('NUM_TYPE', 'num'), ('(', '('),
                      ('REAL', 0.0), (')', ')'), (';', ';'), ('IDENTIFIER', 'q'), (':', ':'),
                      ('LIST_TYPE', 'list'), ('NUM_TYPE', 'num'),('(', '('),  ('*', '*'),
                      (')', ')'), (')', ')')]


def test_variable_declaration():
    lexer = build_lexer()
    lexer.input('a := 1;b := 2; c := 3;')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'a'), ('ASSIGN', ':='), ('REAL', 1.0), (';', ';'),
                      ('IDENTIFIER', 'b'), ('ASSIGN', ':='), ('REAL', 2.0), (';', ';'),
                      ('IDENTIFIER', 'c'), ('ASSIGN', ':='), ('REAL', 3.0), (';', ';')]


def test_lineno():
    lexer = build_lexer()
    lexer.input('a := 1;\nb := 2;')
    tokens = [t for t in lexer]
    assert lexer.lineno == 2
    # reset line counter
    lexer.lineno = 1
    lexer.input('a := 1;\nb := 2;\n c := 3;\n\n\n')
    tokens = [t for t in lexer]
    assert lexer.lineno == 6


def test_illegal_character():
    lexer = build_lexer()
    with pytest.raises(SyntaxError) as error:
        lexer.input('a ~= 1;')
        tokens = [t for t in lexer]
    assert error.value.message.type == 'error'
    assert error.value.message.lineno == 1
    assert error.value.message.value == '~= 1;'
    assert error.value.message.lexpos == 2


def test_comment():
    lexer = build_lexer()
    lexer.input('a := 1; # b := 2;\nc := 3;')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'a'), ('ASSIGN', ':='), ('REAL', 1.0), (';', ';'),
                      ('IDENTIFIER', 'c'), ('ASSIGN', ':='), ('REAL', 3.0), (';', ';')]
