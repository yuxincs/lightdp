from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
import jsonpickle
import json


def test_parser():
    lexer = build_lexer()
    parser = build_parser()
    with open('tests/sparse_vector.ldp', 'r') as f:
        with open('tests/sparse_vector_ast.json', 'r') as ast:
            node = parser.parse(f.read(), lexer=lexer)
            node_dict = json.loads(jsonpickle.encode(node))
            assert node_dict == json.loads(ast.read())
