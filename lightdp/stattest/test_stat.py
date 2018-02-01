import numpy as np


def test_stat(x, y, eps):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """
    return (len(x)) - (np.exp(eps)) * (len(y))  # one of the options


def sig_test_stat(R, eps):
    """
        Function to compute significance of the value of T
    :param R: x and y
    :return: test statistic
    """

    Rcopy = R[:]
    np.random.shuffle(Rcopy)
    k = np.random.binomial(len(Rcopy), np.exp(eps) / (1 + (np.exp(eps))))
    X = Rcopy[:k]
    Y = Rcopy[k:]

    return test_stat(X, Y, eps)
