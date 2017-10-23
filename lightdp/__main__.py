import ast
import jsonpickle
from lightdp import __doc__
from lightdp import verifier


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

    # open the config file if present
    config = None
    if results.config is not None:
        with open(results.config, 'r') as f:
            config = json.loads(f.read())

    all_parse_trees = []
    for file in results.files:
        with open(file, 'r') as f:
            tree = ast.parse(f.read())
            if verifier.verify(tree):
                print(file + ' : satisfiable')
            else:
                print(file + ' : unsatisfiable')

            if results.out is None:
                pass
                # TODO: write the transformed program to the output file
                #with open(file[0:results.files[0].rfind('.')] + '.py', 'w') as out:
                    #out.write(ast.transform(node, config, is_verification=True))
            else:
                all_parse_trees += tree

    if results.out is not None:
        pass
        # TODO: write the transformed program to the output file
        #with open(results.out, 'w') as out:
            #out.write(ast.transform(all_parse_trees, config, is_verification=True))


if __name__ == '__main__':
    main()
