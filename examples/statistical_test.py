from lightdp.stattest import hypothesis_test, generate_inputs, fisher_s_selector, difference_s_selector
from lightdp.stattest.algorithms import noisy_max_v1, sparse_vector
from interval import interval, inf, imath


def main():
    # auto-generated data for sparsevector
    # D1 = [10.747997673023637, 9.176688735248929, 9.685779806342222, 9.276506422051003, 10.14197198493314, 10.777285751217708, 10.033518297158158, 10.739107887579431, 9.466024642462145, 10.046506781898248]
    # D2 = [9.74799, 9.999989999999999, 10.19486, 9.99999, 9.57099, 9.888639999999999, 9.08919, 9.76694, 9.99999, 9.73776]

    # auto-generated data for noisymax
    D1 = [10.047838788362302, 9.156301318712105, 9.934576874381165, 10.818923545533439, 10.964414221707846, 9.814549818258723, 10.343685529387757, 10.270895438249106, 10.422325599687007, 9.498322242077997]
    D2 = [11.04783, 10.10206, 10.85322, 10.04784, 10.04784, 10.40406, 10.04784, 9.664679999999999, 9.660929999999999, 10.06784]

    algorithm_epsilon = 1
    algorithm = noisy_max_v1
    results = []

    for epsilon in [x / 10.0 for x in range(1, 30, 1)]:
        # algorithm's fixed privacy budget
        kwargs = {'eps': algorithm_epsilon}

        # call s selector to find s
        S = fisher_s_selector(algorithm, (), kwargs, D1, D2, epsilon, search_space=[[i] for i in range(10)])

        # run 5 times and output average p value
        avg_p1, avg_p2 = 0.0, 0.0
        for _ in range(5):
            p1, p2 = hypothesis_test(algorithm, (), kwargs, D1, D2, S, epsilon, 10000, cores=1)
            avg_p1 += p1
            avg_p2 += p2
        results.append((epsilon, avg_p1 / 5, avg_p2 / 5))
        print("epsilon: %f, p1 = %f, p2 = %f | S = %s" % (epsilon, avg_p1 / 5, avg_p2 / 5, S))

    # print output
    print("\nFinal Result:")
    print("%s" % algorithm.__name__)
    print("Algorithm epsilon: %f" % algorithm)
    print("D1 : %s" % D1)
    print("D2 : %s" % D2)
    print("[%s]" % (",".join(["[%f, %f, %f]\n" % result for result in results])))


if __name__ == '__main__':
    main()
