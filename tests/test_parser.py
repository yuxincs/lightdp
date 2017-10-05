from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
import lightdp.ast as ast


def test_parser():
    lexer = build_lexer()
    parser = build_parser()

