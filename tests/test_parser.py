from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
import jsonpickle


def test_parser():
    lexer = build_lexer()
    parser = build_parser()
    precondition, type_map = parser.parse('precondition(q[i] >= -1 and q[i] <= 1); T, N, len, epsilon : num(0)', lexer=lexer)
    assert precondition == 'q[i] >= -1 and q[i] <= 1'
    assert jsonpickle.encode(type_map) == """{"N": {"py/object": "lightdp.ast.Type", "left": "num", "right": "0"}, "T": {"py/id": 0}, "epsilon": {"py/id": 0}, "len": {"py/id": 0}}"""
