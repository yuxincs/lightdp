from lightdp.__main__ import main


def test_main():
    assert main(['./examples/sparse_vector.py']) == 0
