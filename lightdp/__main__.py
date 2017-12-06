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
    arg_parser.add_argument('files', metavar='FILE', type=str, nargs='+')
    arg_parser.add_argument('-o', '--out',
                            action='store', dest='out', type=str,
                            help='The output file name.', required=False)
    arg_parser.add_argument('-c', '--config',
                            action='store', dest='config', type=str,
                            help='The configuration file name.', required=False)

    results = arg_parser.parse_args()

    all_parse_trees = []
    for file in results.files:
        with open(file, 'r') as f:
            tree = ast.parse(f.read())
            if verifier.verify(tree):
                print(file + ' : satisfiable')
            else:
                print(file + ' : unsatisfiable')

            transformed = transformer.transform(tree)
            if results.out is None:
                # write the transformed program to the output file
                with open(file[0:results.files[0].rfind('.')] + '_t.py', 'w') as out:
                    out.write(astunparse.unparse(transformed))
            else:
                all_parse_trees.append(transformed)

    if results.out is not None:
        # TODO: write the transformed program to the output file
        with open(results.out, 'w') as out:
            for transformed in transformer.transform(all_parse_trees):
                out.write(astunparse.unparse(transformed))


if __name__ == '__main__':
    main()
