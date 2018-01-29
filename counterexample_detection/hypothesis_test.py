from noisymax import noisymax
from sparsevector import sparsevector
from s_selector import s_selector
from test_stat import test_stat
from sig_test_stat import sig_test_stat
import matplotlib.pyplot as plt
import numpy as np

D1 = [9.917370926052758, 10.295232500311627, 10.979253058964114, 10.954906274017656,
      9.205904120344211, 10.52166922332997, 9.17760719515679, 9.830086654150426, 9.544008376222147, 10.034087353065718]

D2 = [9.91737, 10.0, 10.0, 10.31766, 8.39766, 9.62791, 9.99999, 10.48255, 9.99999, 9.86943]
n=1000
eps1=2
eps2=2

def hypothesis_test(algo,D1,D2,eps1,n):
    # check if input queries are valid
    assert all(abs(a - b) <= 1 for a, b in zip(D1, D2))

    # choose an S
    S = s_selector(algo)

    # compute test statistic T
    x,y=[],[]

    for i in range(n):
        a = noisymax(D1, eps1)
        b = noisymax(D2, eps1)
        if a in S:
            x.append(a)
        if b in S:
            y.append(b)

    T1 = test_stat(x, y, n,eps2)
    T2 = test_stat(y, x, n,eps2)

    # compute significance of the value of T
    R=x+y
    ti=[sig_test_stat(R,eps2,n) for _ in range(n)]

    result = [eps1, sum([x >= T1 for x in ti]) / n, sum([x >= T2 for x in ti]) / n]

    return result

