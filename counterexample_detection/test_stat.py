import numpy as np

def test_stat(x, y, n, eps):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """
    return (len(x) / float(n)) - (np.exp(eps)) * (len(y) / float(n))  # one of the options