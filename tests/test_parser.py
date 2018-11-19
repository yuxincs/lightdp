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
    assert type_map == jsonpickle.decode("""{"N": {"py/object": "lightdp.verifier.typing.NumType", "value": "0"}, "T": {"py/id": 0}, "T_threshold": {"py/object": "lightdp.verifier.typing.NumType", "value": "1"}, "c1": {"py/object": "lightdp.verifier.typing.NumType", "value": "0"}, "c2": {"py/id": 2}, "epsilon": {"py/id": 0}, "eta_1": {"py/id": 1}, "eta_2": {"py/object": "lightdp.verifier.typing.NumType", "value": "2 if q[i]+eta_2>=T_threshold else 0"}, "i": {"py/id": 2}, "len": {"py/id": 0}, "out": {"py/object": "lightdp.verifier.typing.ListType", "elem_type": {"py/object": "lightdp.verifier.typing.BoolType"}}, "q": {"py/object": "lightdp.verifier.typing.ListType", "elem_type": {"py/object": "lightdp.verifier.typing.NumType", "value": "*"}}}""")