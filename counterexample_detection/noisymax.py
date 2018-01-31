import numpy as np
from collections import Counter

D1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
D2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]

eps=2

def noisymax(Q, eps):

    # add lapalce noise
    noisy_array = [a + np.random.laplace(scale=1.0 / eps) for a in Q]

    # compare the largest noisy element and return the index of primal query along with the max value
    return np.argmax(noisy_array)

if __name__=="__main__":
    for eps in range(3,15):
        a = [noisymax(D1, eps) for _ in range(10000)]
        b = [noisymax(D2, eps) for _ in range(10000)]
        print(Counter(a + b))