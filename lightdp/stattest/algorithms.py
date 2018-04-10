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
    while i < len(Q):
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
    N=len(Q)
    c1, c2, i = 0, 0, 0
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    while i < len(Q) and c1<N:
        eta2 = np.random.laplace(scale=4.0*N / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(Q[i] + eta2)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return out


def sparse_vector_v4(Q, eps, N, T):
    N=1
    c1, c2, i = 0, 0, 0
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    while i < len(Q) and c1 < N:
        eta2 = np.random.laplace(scale=4.0*N / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1
    return out


def svt_v1(Q, eps, N, T):
    out = []
    delta = len(Q)
    eta1 = np.random.laplace(scale=2.0 * delta / eps)
    noisy_T = T + eta1
    count = 0
    for q in Q:
        eta2 = np.random.laplace(scale=4.0 * N * delta / eps)
        if (q + eta2) > noisy_T:
            out.append(True)
            count += 1
            if count >= N:
                break
        else:
            out.append(False)
    hdist = 0
    for index, value in enumerate(out):
        if index < len(Q) / 2 and value == True:
            hdist += 1
        if index >= len(Q) / 2 and value == False:
            hdist += 1
    return hdist


def svt_v3(Q, eps, N, T):
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    noisy_T = T + eta1
    count = 0
    for q in Q:
        eta2 = np.random.laplace(scale=2.0 * N / eps)
        if q + eta2 > noisy_T:
            out.append(q+eta2)
            count += 1
            if count >= N:
                break
        else:
            out.append(False)
    return out.count(False)


def svt_v4(Q, eps, N, T):
    out = []
    delta = 1
    eta1 = np.random.laplace(scale=4.0 * delta / eps)
    noisy_T = T + eta1
    count = 0
    for q in Q:
        eta2 = np.random.laplace(scale=(4.0 * delta) / (3.0 * eps))
        if (q + eta2) > noisy_T:
            out.append(True)
            count += 1
            if count >= N:
                break
        else:
            out.append(False)
    hdist = 0
    for index, value in enumerate(out):
        if index < len(Q) / 2 and value == True:
            hdist += 1
        if index >= len(Q) / 2 and value == False:
            hdist += 1
    return hdist


def svt_v5(Q, eps, N, T):
    out = []
    delta = 1
    eta1 = np.random.laplace(scale=2.0 * delta / eps)
    noisy_T = T + eta1
    for q in Q:
        eta2 = 0
        if (q + eta2) >= noisy_T:
            out.append(True)
        else:
            out.append(False)
    hdist = 0
    for index, value in enumerate(out):
        if index < len(Q) / 2 and value == True:
            hdist += 1
        if index >= len(Q) / 2 and value == False:
            hdist += 1
    return hdist



def svt_v6(Q, eps, N, T):
    out = []
    delta = 1
    eta1 = np.random.laplace(scale=2.0 * delta / eps)
    noisy_T = T + eta1
    for q in Q:
        eta2 = np.random.laplace(scale=2.0 * delta / eps)
        if (q + eta2) >= noisy_T:
            out.append(True)
        else:
            out.append(False)
    hdist = 0
    for index, value in enumerate(out):
        if index < len(Q) / 2 and value == True:
            hdist += 1
        if index >= len(Q) / 2 and value == False:
            hdist += 1
    return hdist