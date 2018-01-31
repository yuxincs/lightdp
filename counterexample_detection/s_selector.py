from inspect import isfunction
from collections import Counter
from noisymax import noisymax
from sparsevector import sparsevector

D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]

# D1 = [9.917370926052758, 10.295232500311627, 10.979253058964114, 10.954906274017656,
#       9.205904120344211, 10.52166922332997, 9.17760719515679, 9.830086654150426, 9.544008376222147, 10.034087353065718]
#
# D2 = [9.91737, 10.0, 10.0, 10.31766, 8.39766, 9.62791, 9.99999, 10.48255, 9.99999, 9.86943]

eps=2

def s_selector(algo,D1,D2,eps):

    assert isfunction(algo)

    if algo==noisymax:
        return [8,4,0]

    elif algo==sparsevector:
        a = [algo(D1, eps) for _ in range(1000)]
        b = [algo(D2, eps) for _ in range(1000)]

        countitem=Counter(a+b).most_common(2)

        return [countitem[0][0],countitem[1][0]]

if __name__=="__main__":
    for eps in range(3,15):
        print(s_selector(sparsevector,D1,D2,eps))