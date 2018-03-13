# TODO: the whole package should be removed in the future since we should have user-input algorithms

import numpy as np


def noisy_max_v1a(Q, eps):
    # add laplace noise
    noisy_array = [a + np.random.laplace(scale=2.0 / eps) for a in Q]

    # find the largest noisy element and return its index
    return np.argmax(noisy_array)


def noisy_max_v1b(Q, eps):
    noisy_array = [a + np.random.laplace(scale=2.0 / eps) for a in Q]
    return max(noisy_array)


def noisy_max_v2a(Q, eps):
    noisy_array = [a + np.random.exponential(scale=2.0 / eps) for a in Q]
    return np.argmax(noisy_array)


def noisy_max_v2b(Q, eps):
    noisy_array = [a + np.random.exponential(scale=2.0 / eps) for a in Q]
    return max(noisy_array)


def histogram(Q, eps):
    noisy_array = [a + np.random.exponential(scale=1.0 / eps) for a in Q]
    return noisy_array[0]


def sparse_vector(Q, eps, N, T):
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
    return out


def sparse_vector_v1(Q, eps, N, T):
    out = []
    c1, c2, i = 0, 0, 0
    while i < len(Q) and c1 < N:
        eta = np.random.laplace(scale=4.0 * N / eps)
        if Q[i] + eta >= T:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return c2


def sparse_vector_v2(Q, eps, N, T):
    out = []
    c1, c2, i = 0, 0, 0
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    while i < len(Q) and c1 < N:
        eta2 = np.random.laplace(scale=4.0 / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return out


def sparse_vector_v3(Q, eps, N, T):
    out = []
    c1, c2, i = 0, 0, 0
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    while i < len(Q):
        eta2 = np.random.laplace(scale=4.0*N / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return c1


def sparse_vector_v4(Q, eps, N, T):
    out = []
    c1, c2, i = 0, 0, 0
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    while i < len(Q) and c1 < 1:
        eta2 = np.random.laplace(scale=4.0*N / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return c1