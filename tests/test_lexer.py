import pytest
from lightdp.verifier.lexer import build_lexer


def test_precondition():
    lexer = build_lexer()
    lexer.input('precondition : (q[i] >= -1 and q[i] <= 1);')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('PRECONDITION', 'precondition'), (':', ':'), ('EXPRESSION', 'q[i] >= -1 and q[i] <= 1'),
                      (';', ';')]


def test_precondition_with_forall():
    lexer = build_lexer()
    lexer.input('precondition : forall i (q[i] >= -1 and q[i] <= 1);')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('PRECONDITION', 'precondition'), (':', ':'), ('FORALL', 'forall'), ('IDENTIFIER', 'i'),
                      ('EXPRESSION', 'q[i] >= -1 and q[i] <= 1'), (';', ';')]


def test_type_declaration():
    lexer = build_lexer()
    lexer.input('T : num(0); a, b : num(*); c : list bool; d: list num(0);')
    tokens = [(t.type, t.value) for t in lexer]
    assert tokens == [('IDENTIFIER', 'T'), (':', ':'), ('NUM_TYPE', 'num'), ('EXPRESSION', '0'), (';', ';'),
                      ('IDENTIFIER', 'a'), (',', ','), ('IDENTIFIER', 'b'), (':', ':'), ('NUM_TYPE', 'num'), ('*', '*'), (';', ';'),
                      ('IDENTIFIER', 'c'), (':', ':'), ('LIST_TYPE', 'list'), ('BOOL_TYPE', 'bool'), (';', ';'),
                      ('IDENTIFIER', 'd'), (':', ':'), ('LIST_TYPE', 'list'), ('NUM_TYPE', 'num'), ('EXPRESSION', '0'), (';', ';')]


def test_lineno():
    lexer = build_lexer()
    lexer.input('precondition(1 > 2);\nT : num(0);')
    tokens = [t for t in lexer]
    assert lexer.lineno == 2
    # reset line counter
    lexer.lineno = 1
    lexer.input('T : num(0);\nT : num(0);\nT : num(0);\n\n\n')
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
