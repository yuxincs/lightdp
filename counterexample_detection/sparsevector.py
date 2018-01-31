import numpy as np
from collections import Counter

SD1 = [9.917370926052758, 10.295232500311627, 10.979253058964114, 10.954906274017656,
      9.205904120344211, 10.52166922332997, 9.17760719515679, 9.830086654150426, 9.544008376222147, 10.034087353065718]

SD2 = [9.91737, 10.0, 10.0, 10.31766, 8.39766, 9.62791, 9.99999, 10.48255, 9.99999, 9.86943]

eps=2

def sparsevector(Q,eps):
    T=10
    out = []
    eta1 = np.random.laplace(scale=2.0 / eps)
    Tbar = T + eta1
    c1, c2, i = 0, 0, 0
    while i < len(Q):
        eta2 = np.random.laplace(scale=4 * T / eps)
        if Q[i] + eta2 >= Tbar:
            out.append(True)
            c1 += 1
        else:
            out.append(False)
            c2 += 1
        i += 1

    return sum(out)

if __name__=="__main__":
    for eps in range(3,15):
        a=[sparsevector(SD1,eps) for _ in range(10000)]
        b=[sparsevector(SD2,eps) for _ in range(10000)]
        print(Counter(a+b))