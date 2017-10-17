from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
from lightdp import __doc__
from lightdp import ast


def main():
    import argparse
    import json
    arg_parser = argparse.ArgumentParser(description=__doc__)
    arg_parser.add_argument('files', metavar='FILE', type=str, nargs='+')
    arg_parser.add_argument('-o', '--out',
                            action='store', dest='out', type=str,
                            help='The output file name.', required=False)
    arg_parser.add_argument('-c', '--config',
                            action='store', dest='config', type=str,
                            help='The configuration file name.', required=False)

    results = arg_parser.parse_args()

    # build lexer and parser
    lexer = build_lexer()
    parser = build_parser()

    # open the config file if present
    config = None
    if results.config is not None:
        with open(results.config, 'r') as f:
            config = json.loads(f.read())

    import jsonpickle
    all_parse_trees = []
    for file in results.files:
        with open(file, 'r') as f:
            node = parser.parse(f.read(), lexer=lexer)
            if results.out is None:
                with open(file[0:results.files[0].rfind('.')] + '.py', 'w') as out:
                    out.write(ast.transform(node, config, is_verification=True))
            else:
                all_parse_trees += node

    if results.out is not None:
        with open(results.out, 'w') as out:
            out.write(ast.transform(all_parse_trees, config, is_verification=True))


if __name__ == '__main__':
    main()
