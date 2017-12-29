import ast
from lightdp import __doc__
from lightdp import verifier, transformer


def main():
    """
    Main function, parse the program argument and run the program.
    :return: None
    """
    import argparse
    import astunparse

    arg_parser = argparse.ArgumentParser(description=__doc__)
    arg_parser.add_argument('file', metavar='FILE', type=str, nargs=1)
    arg_parser.add_argument('-o', '--out',
                            action='store', dest='out', type=str,
                            help='The output file name.', required=False)
    arg_parser.add_argument('-j', '--json',
                            action='store', dest='json_file', type=str,
                            help='Output all results in json format.', required=False)

    results = arg_parser.parse_args()
    results.file = results.file[0]
    results.out = results.file[0:results.file.rfind('.')] + '_t.py' if results.out is None else results.out

    # parse / verify / transform the file
    with open(results.file, 'r') as f:
        tree = ast.parse(f.read())
        is_sat, constraints = verifier.verify(tree)
        transformed = None
        if not is_sat:
            with open(results.out, 'w') as out:
                transformed = transformer.transform(tree)
                out.write(transformed)

        if results.json_file is not None:
            with open(results.json_file, 'w') as out:
                import json
                json.dump({
                    'is_sat': is_sat,
                    'constraints': constraints,
                    'transformed': transformed
                }, out)

        # print('\033[32;1mFinal Constraint:\033[0m')
        # print(in_file + ' : satisfiable' if is_sat else ' : unsatisfiable')


if __name__ == '__main__':
    main()
