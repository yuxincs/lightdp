from lightdp.stattest import hypothesis_test, difference_test_stat, division_test_stat, \
    sig_test_stat, generate_inputs, difference_s_selector
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
    results = []
    args = ()
    for eps in [x / 10.0 for x in range(29, 50, 1)]:
        kwargs = {'eps': eps}
        avg_p1, avg_p2 = 0, 0
        S = difference_s_selector(noisymax, args, kwargs, D1, D2)
        for i in range(5):
            p1, p2 = hypothesis_test(noisymax, args, kwargs, D1, D2,
                                     S,
                                     difference_test_stat(2), sig_test_stat(2), 1000, 0)
            avg_p1 += p1
            avg_p2 += p2
        print("epsilon: %f, p1 = %f, p2 = %f | S = %s" % (eps, avg_p1 / 5, avg_p2 / 5, S))
        results.append((eps, avg_p1 / 5, avg_p2 / 5))

    # print output
    print("\nFinal Result:")
    print("D1 : %s" % D1)
    print("D2 : %s" % D2)
    print("[%s]" % (",".join(["[%f, %f, %f]\n" % result for result in results])))


if __name__ == '__main__':
    main()
