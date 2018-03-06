# TODO: the whole package should be removed in the future since we should have user-input algorithms

import numpy as np


def noisymax(Q, eps):

    # add lapalce noise
    noisy_array = [a + np.random.laplace(scale=1.0 / eps) for a in Q]

    # compare the largest noisy element and return the index of primal query along with the max value
    return np.argmax(noisy_array)


def sparsevector(Q, eps, N, T):
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    c1, c2, i = 0, 0, 0
    while i < len(Q):
        eta2 = np.random.laplace(scale=4 * N / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1

    return sum(out)
