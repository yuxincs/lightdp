from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
import jsonpickle


def test_forall_keyword():
    docstring = \
        """
        precondition : forall i (^q[i] >= -1 and ^q[i] <= 1);
        A : num(0)
        """
    lexer = build_lexer()
    parser = build_parser()
    forall_var, precondition, type_map = parser.parse(docstring, lexer=lexer)
    assert forall_var == ['i']


def test_parser():
    docstring = \
        """
        precondition : (^q[i] >= -1 and ^q[i] <= 1 and ^out[i] == 0);
        T, N, len, epsilon : num(0); q : list num(*); out : list bool;
        c1, c2, i : num(0); T_threshold, eta_1 : num(1); eta_2 : num(2 if q[i]+eta_2>=T_threshold else 0)
        """
    lexer = build_lexer()
    parser = build_parser()
    forall_var, precondition, type_map = parser.parse(docstring, lexer=lexer)
    assert forall_var is None
    assert precondition == "^q[i] >= -1 and ^q[i] <= 1 and ^out[i] == 0"
    assert type_map == jsonpickle.loads(r'{"py/reduce": [{"py/type": "collections.OrderedDict"}, {"py/tuple": []}, null, null, {"py/tuple": [{"py/tuple": ["T", {"py/object": "lightdp.typing.NumType", "value": "0"}]}, {"py/tuple": ["N", {"py/id": 1}]}, {"py/tuple": ["len", {"py/id": 1}]}, {"py/tuple": ["epsilon", {"py/id": 1}]}, {"py/tuple": ["q", {"py/object": "lightdp.typing.ListType", "elem_type": {"py/object": "lightdp.typing.NumType", "value": "*"}}]}, {"py/tuple": ["out", {"py/object": "lightdp.typing.ListType", "elem_type": {"py/object": "lightdp.typing.BoolType"}}]}, {"py/tuple": ["c1", {"py/object": "lightdp.typing.NumType", "value": "0"}]}, {"py/tuple": ["c2", {"py/id": 6}]}, {"py/tuple": ["i", {"py/id": 6}]}, {"py/tuple": ["T_threshold", {"py/object": "lightdp.typing.NumType", "value": "1"}]}, {"py/tuple": ["eta_1", {"py/id": 7}]}, {"py/tuple": ["eta_2", {"py/object": "lightdp.typing.NumType", "value": "2 if q[i]+eta_2>=T_threshold else 0"}]}]}]}')
