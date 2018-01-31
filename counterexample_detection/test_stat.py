import numpy as np

def test_stat(x, y, n, eps,option,c):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """

    if option==1:
        return (len(x) / float(n)) - (np.exp(eps)) * (len(y) / float(n))
    elif option==2:
        return (len(x) / float(n)+c)/(len(y) / float(n)+c)