from lightdp.stattest import hypothesis_test, test_stat, sig_test_stat, generate_inputs, s_selector
from lightdp.stattest.algorithms import noisymax, sparsevector


def main():
    # database for sparsevector
    """
    D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
    D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]
    """

    # database for noisymax
    D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
    D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]

    # auto-generated data for sparsevector

    """
    D1 = [9.917370926052758, 10.295232500311627, 10.979253058964114, 10.954906274017656,
          9.205904120344211, 10.52166922332997, 9.17760719515679, 9.830086654150426, 9.544008376222147,
          10.034087353065718]

    D2 = [9.91737, 10.0, 10.0, 10.31766, 8.39766, 9.62791, 9.99999, 10.48255, 9.99999, 9.86943]
    """

    for eps in [x / 10.0 for x in range(70, 90, 1)]:
        p1, p2 = hypothesis_test(noisymax, (), {'eps': 2}, eps, D1, D2, s_selector(noisymax),
                                 test_stat, sig_test_stat, 10000, 1)
        print(eps, p1, p2)


if __name__ == '__main__':
    main()
