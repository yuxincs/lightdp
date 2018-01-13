import numpy as np
from collections import Counter
import multiprocessing as mp
import math


# Create two values of input which satisfies the property of input query, along with some hyperparameters
D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]
diff = [a - b for a, b in zip(D1, D2)]
eps1 = 4
eps2 = 2
T = 5
N = 2
n = 10000


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


def test_stat(x, y, eps):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """
    return (len(x) / n) - (np.exp(eps)) * (len(y) / n)  # one of the options


def sig_test_stat(R, eps):
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
    return test_stat(X, Y, eps)


def main():
    # check if input queries are valid to use
    if all(abs(x) <= 1 for x in diff):
        print('Valid Input')
    else:
        print('Invalid Input')

    # to find a reasonable S

    # for eps in range(2,10):
    #     A=[]
    #     B=[]
    #     for i in range(100000):
    #         A.append(noisymax(D1,eps))
    #         B.append(noisymax(D2,eps))
    #     print(Counter(A+B))

    def calc_xy(id, func, D1, D2, S, eps1, eps2, n, result_queue):
        print('[Process-%d] Started with %d' % (id, n))
        x = []
        y = []
        for _ in range(n):
            a = func(D1, eps1)
            b = func(D2, eps1)
            if a in S:
                x.append(a)
            if b in S:
                y.append(b)

        T1 = test_stat(x, y, eps2)
        T2 = test_stat(y, x, eps2)

        # compute significance of test statistic
        R = x + y
        ti1 = []
        ti2 = []
        for i in range(n):
            ti1.append(sig_test_stat(R, eps2))
            ti2.append(sig_test_stat(R, eps2))

        result_queue.put((sum([x >= T1 for x in ti1]), sum([x >= T2 for x in ti2])))
        print('[Process-%d] Finished' % id)
        return

    S = [7, 4, 2]

    # noisymax:
    for eps1 in range(2, 10):
        # compute test statistic
        result_queue = mp.Queue()
        processes = []

        for i in range(mp.cpu_count()):
            process = mp.Process(target=calc_xy, args=(i, noisymax, D1, D2, S, eps1, eps2,
                                                       int(math.ceil(float(n) / mp.cpu_count())), result_queue))
            processes.append(process)
            process.start()

        print('Generate %d processes for %s function' % (mp.cpu_count(), 'NoisyMax'))

        for process in processes:
            process.join()

        print('Work finished, merge the results')

        # merge the results
        value1 = 0
        value2 = 0
        for _ in range(len(processes)):
            local_v1, local_v2 = result_queue.get()
            value1 += local_v1
            value2 += local_v2

        result = [eps1, float(value1) / n, float(value2) / n]
        # compute p value
        print(str(result))

    # find appropriate S for sparse vector
    # for eps in range(2,10):
    #     A=[]
    #     B=[]
    #     for i in range(100000):
    #         A.append(sparsevector(T,N,4,D1))
    #         B.append(sparsevector(T,N,4,D2))
    #     print(Counter(A+B))

    S = [3, 2]
    # TODO: sparse vector can be merged
    # sparse vector:
    """
    for eps1 in range(2,10):
        # compute test statistic
        x=[]
        y=[]
        for i in range(n):
            a=sparsevector(T,N,eps1,D1)
            b=sparsevector(T,N,eps1,D2)
            if a in S:
                x.append(a)
            if b in S:
                y.append(b)
        T1=test_stat(x,y,eps2)
        T2=test_stat(y,x,eps2)

            # compute significance of test statistic

        R=x+y
        ti1=[]
        ti2=[]
        for i in range(n):
            ti1.append(sig_test_stat(R,eps2))
            ti2.append(sig_test_stat(R,eps2))

        result=[eps1,sum([x>=T1 for x in ti1])/n,sum([x>=T2 for x in ti2])/n]
        # compute p value
        print(str(result))
        """

if __name__=="__main__":
   main()
