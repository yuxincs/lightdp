import numpy as np


def difference_test_stat(eps):
    return lambda x, y: (len(x)) - (np.exp(eps)) * (len(y))


def division_test_stat(c):
    return lambda x, y: float(len(x) + c) / (len(y) + c)


def sig_test_stat(eps):
    def __sig_test_stat(R, test_stat):
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
        return test_stat(X, Y)

    return __sig_test_stat
