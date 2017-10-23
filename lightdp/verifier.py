import ast
import _ast


def verify(tree):
    assert isinstance(tree, _ast.AST)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            precodition, type_map = __parse_docstring(ast.get_docstring(node))
            # TODO: do type inference here


def __parse_docstring(s):
    assert s is not None
    from lightdp.lexer import build_lexer
    from lightdp.parser import build_parser
    lexer = build_lexer()
    parser = build_parser()
    return parser.parse(s, lexer=lexer)
