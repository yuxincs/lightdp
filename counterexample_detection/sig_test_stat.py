import numpy as np
from test_stat import test_stat

def sig_test_stat(R, eps,n):
    """
        Function to compute significance of the value of T
    :param R: x and y
    :return: test statistic
    """

    Rcopy=R[:]
    np.random.shuffle(Rcopy)
    k=np.random.binomial(len(Rcopy),np.exp(eps) / (1 + (np.exp(eps))))
    X=Rcopy[:k]
    Y=Rcopy[k:]

    return test_stat(X, Y, n, eps)
