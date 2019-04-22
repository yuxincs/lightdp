import ast
import argparse
import astunparse
import logging
import os
import coloredlogs
from lightdp import __doc__
from lightdp import verify, transform

coloredlogs.install('INFO', fmt='%(asctime)s %(levelname)s %(message)s')
logger = logging.getLogger(__name__)


def main():
    """
    Main function, parse the program argument and run the program.
    :return: None
    """

    arg_parser = argparse.ArgumentParser(description=__doc__)
    arg_parser.add_argument('file', metavar='FILE', type=str, nargs=1)
    arg_parser.add_argument('-o', '--out',
                            action='store', dest='out', type=str,
                            help='The output file name.', required=False)
    arg_parser.add_argument('-c', '--constraints',
                            action='store', dest='constraints', type=str,
                            help='Output all constraints to file.', required=False)

    results = arg_parser.parse_args()
    results.file = results.file[0]
    results.out = results.out if results.out else \
        './{}_t.py'.format(os.path.splitext(os.path.basename(results.file))[0])
    results.constraints = results.constraints if results.constraints else \
        './{}_constraints.txt'.format(os.path.splitext(os.path.basename(results.file))[0])

    # parse / verify / transform the file
    with open(results.file, 'r') as f:
        tree = ast.parse(f.read())
        is_sat, constraints = verify(tree)
        if not is_sat:
            logger.info('Type check succeeds, now transforming the algorithm...')
            with open(results.out, 'w') as out:
                out.write(astunparse.unparse(transform(tree)))
            logger.info('Transformation finished at {}. See {} for constraints generated.'
                        .format(results.out, results.constraints))
        else:
            logger.info('Type check fails, the algorithm does not satisfy differential privacy.'
                        'See {} for constraints used.'.format(results.constraints))

        with open(results.constraints, 'w') as out:
            out.write(constraints)


if __name__ == '__main__':
    main()
