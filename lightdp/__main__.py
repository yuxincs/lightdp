from lightdp.lexer import build_lexer
from lightdp.parser import build_parser
from lightdp import __doc__


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', metavar='FILE', type=str, nargs='+')
    parser.add_argument('-o', '--out',
                        action='store', dest='out', type=str,
                        help='The output file name.', required=False)

    results = parser.parse_args()
    if results.out is None:
        results.out = results.files[0][0:results.files[0].rfind('.')] + '.py'
    print('Files: ' + json.dumps(results.files))
    print('Out: ' + results.out)

    # build lexer and parser
    lexer = build_lexer()
    parser = build_parser()

    for file in results.files:
        with open(file, 'r') as f:
            parser.parse(f.read(), lexer=lexer)


if __name__ == '__main__':
    main()
