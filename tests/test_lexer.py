import pytest
from lightdp.lexer import build_lexer


def test_function_declaration():
    lexer = build_lexer()
    lexer.input('function SparseVector(T, N, epsilon : num(0); q : list num(*))')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('FUNCTION', 'function'), ('IDENTIFIER', 'SparseVector'), ('(', '('),
                      ('IDENTIFIER', 'T'), (',', ','), ('IDENTIFIER', 'N'), (',', ','),
                      ('IDENTIFIER', 'epsilon'), (':', ':'), ('NUM_TYPE', 'num'), ('(', '('),
                      ('REAL', 0.0), (')', ')'), (';', ';'), ('IDENTIFIER', 'q'), (':', ':'),
                      ('LIST_TYPE', 'list'), ('NUM_TYPE', 'num'), ('(', '('),  ('*', '*'),
                      (')', ')'), (')', ')')]


def test_variable_declaration():
    lexer = build_lexer()
    lexer.input('a := 1;b := 2; c := 3;')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'a'), ('ASSIGN', ':='), ('REAL', 1.0), (';', ';'),
                      ('IDENTIFIER', 'b'), ('ASSIGN', ':='), ('REAL', 2.0), (';', ';'),
                      ('IDENTIFIER', 'c'), ('ASSIGN', ':='), ('REAL', 3.0), (';', ';')]


def test_if_else():
    lexer = build_lexer()
    lexer.input('if(a >= T)\n{ out := true::out; }\nelse{\nout := false::out;}')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IF', 'if'), ('(', '('), ('IDENTIFIER', 'a'), ('GE', '>='), ('IDENTIFIER', 'T'),
                      (')', ')'), ('{', '{'), ('IDENTIFIER', 'out'), ('ASSIGN', ':='),
                      ('BOOLEAN', True), (':', ':'), (':', ':'), ('IDENTIFIER', 'out'), (';', ';'),
                      ('}', '}'), ('ELSE', 'else'), ('{', '{'), ('IDENTIFIER', 'out'),
                      ('ASSIGN', ':='), ('BOOLEAN', False), (':', ':'), (':', ':'), ('IDENTIFIER', 'out'),
                      (';', ';'), ('}', '}')]


def test_not():
    lexer = build_lexer()
    lexer.input('if(!T)')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IF', 'if'), ('(', '('), ('!', '!'), ('IDENTIFIER', 'T'), (')', ')')]


def test_question():
    lexer = build_lexer()
    lexer.input('a ? b : c;')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'a'), ('?', '?'), ('IDENTIFIER', 'b'), (':', ':'),
                      ('IDENTIFIER', 'c'), (';', ';')]


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
    assert error.value.msg.type == 'error'
    assert error.value.msg.lineno == 1
    assert error.value.msg.value == '~= 1;'
    assert error.value.msg.lexpos == 2


def test_comment():
    lexer = build_lexer()
    lexer.input('a := 1; # b := 2;\nc := 3;')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'a'), ('ASSIGN', ':='), ('REAL', 1.0), (';', ';'),
                      ('IDENTIFIER', 'c'), ('ASSIGN', ':='), ('REAL', 3.0), (';', ';')]
