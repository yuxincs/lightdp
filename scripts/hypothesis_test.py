import numpy as np
from collections import Counter
import multiprocessing as mp
import math
import os
import codecs


def noisymax(Q, eps):
    """
        Here use noisy max algorithm as a test case.
        The noise source will be laplace mechanism.
        Here the largest noise element is returned instead of the index of primal query.

    :param Q: The input query
    :param eps: parameter of lapalce mechanism
    :return: index of maximum value from noisy result
    """
    # add lapalce noise
    noisy_array = [a + np.random.laplace(scale=1.0 / eps) for a in Q]

    # compare the largest noisy element and return the index of primal query along with the max value
    return np.argmax(noisy_array)


def sparsevector(T, N, eps, q):
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    c1, c2, i = 0, 0, 0
    while c1 < N and i < len(q):
        eta2 = np.random.laplace(scale=4 * N / eps)
        if q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1

    return len(out)


# TODO: eps can be designed cleaner
def test_stat(x, y, n, eps=2):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """
    return (len(x) / n) - (np.exp(eps)) * (len(y) / n)  # one of the options


def hypothesis_test(algorithm, D1, D2, args, iterations, stat_test_func, S_selector, cores=0):
    def calc(p_id, func, D1, D2, S, args, n, result_queue):
        # print('[Process-%d] Started with %d' % (id, n))
        # reseed the numpy random module
        np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
        x = []
        y = []
        for _ in range(n):
            a = func(D1, *args)
            b = func(D2, *args)
            if a in S:
                x.append(a)
            if b in S:
                y.append(b)

        T1 = stat_test_func(x, y, iterations)
        T2 = stat_test_func(y, x, iterations)

        # compute significance of test statistic
        # TODO : eps argument can be designed cleaner
        def sig_test_stat(R, eps=2):
            """
                Function to compute significance of the value of T
            :param R: x and y
            :return: test statistic
            """
            X = []
            Y = []
            for i in R:
                if np.exp(eps) / (1 + (np.exp(eps))) >= np.random.random():
                    X.append(i)
                else:
                    Y.append(i)
            return stat_test_func(X, Y, iterations, eps)

        R = x + y
        ti1 = []
        ti2 = []
        for _ in range(n):
            ti1.append(sig_test_stat(R))
            ti2.append(sig_test_stat(R))

        result_queue.put((sum([x >= T1 for x in ti1]), sum([x >= T2 for x in ti2])))
        # print('[Process-%d] Finished' % id)
        return

    # compute test statistics
    process_count = mp.cpu_count() if cores == 0 else cores
    result_queue = mp.Queue()
    processes = []
    for p_id in range(process_count):
        process_iterations = int(math.floor(float(iterations) / process_count))
        process_iterations += iterations % process_iterations if p_id == process_count - 1 else 0
        process = mp.Process(target=calc, args=(p_id, algorithm, D1, D2, S_selector(algorithm), args,
                                                process_iterations, result_queue))
        processes.append(process)
        process.start()

    # print('Generate %d processes for %s function' % (mp.cpu_count(), 'NoisyMax'))

    for process in processes:
        process.join()

    # print('Work finished, merge the results')

    # merge the results
    value1 = 0
    value2 = 0
    for _ in range(process_count):
        local_v1, local_v2 = result_queue.get()
        value1 += local_v1
        value2 += local_v2

    # compute p value
    return args[0], float(value1) / iterations, float(value2) / iterations


def main():
    # create two values of input which satisfies the property of input query, along with some hyperparameters
    D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
    D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]
    # check if input queries are valid to use
    assert all(abs(a - b) <= 1 for a, b in zip(D1, D2))
    n = 1000

    # hand-picked S for the two algorithms
    def S_selector(algorithm):
        # to find a reasonable S

        # for eps in range(2,10):
        #     A=[]
        #     B=[]
        #     for i in range(100000):
        #         A.append(noisymax(D1,eps))
        #         B.append(noisymax(D2,eps))
        #     print(Counter(A+B))

        # find appropriate S for sparse vector
        # for eps in range(2,10):
        #     A=[]
        #     B=[]
        #     for i in range(100000):
        #         A.append(sparsevector(T,N,4,D1))
        #         B.append(sparsevector(T,N,4,D2))
        #     print(Counter(A+B))
        from inspect import isfunction

        assert isfunction(algorithm)
        if algorithm.__name__ == 'noisymax':
            return [7, 4, 2]
        if algorithm.__name__ == 'sparsevector':
            return [3, 2]

    # NoisyMax test
    for eps in range(7, 15):
        res = hypothesis_test(noisymax, D1, D2, (eps, ), n, test_stat, S_selector)
        print(res)
    # TODO: bring back the sprase vector test


if __name__=="__main__":
    main()
