from lightdp.scanner import Scanner


def test_parser():
    with open('tests/sparse_vector.ldp', 'r') as f:
        scanner = Scanner()
        scanner.scan(f.read())
