from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
from lightdp import __doc__
from lightdp import ast


def main():
    import argparse
    arg_parser = argparse.ArgumentParser(description=__doc__)
    arg_parser.add_argument('files', metavar='FILE', type=str, nargs='+')
    arg_parser.add_argument('-o', '--out',
                            action='store', dest='out', type=str,
                            help='The output file name.', required=False)

    results = arg_parser.parse_args()


    # build lexer and parser
    lexer = build_lexer()
    parser = build_parser()

    import jsonpickle
    all_parse_trees = []
    for file in results.files:
        with open(file, 'r') as f:
            node = parser.parse(f.read(), lexer=lexer)
            if results.out is None:
                with open(file[0:results.files[0].rfind('.')] + '.py', 'w') as out:
                    out.write(ast.transform(node))
            else:
                all_parse_trees += node

    if results.out is not None:
        with open(results.out, 'w') as out:
            out.write(ast.transform(all_parse_trees))


if __name__ == '__main__':
    main()
