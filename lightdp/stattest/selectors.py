from inspect import isfunction
from collections import Counter
import math


def frequency_s_selector(algorithm, args, kwargs, D1, D2, iterations=1000):
    assert isfunction(algorithm)
    if algorithm.__name__ == 'noisymax':
        return [8, 4, 0]
    if algorithm.__name__ == 'sparsevector':
        return [9]


def difference_s_selector(algorithm, args, kwargs, D1, D2, iterations=1000):
    assert isfunction(algorithm)
    a = [algorithm(D1, *args, **kwargs) for _ in range(iterations)]
    b = [algorithm(D2, *args, **kwargs) for _ in range(iterations)]
    count_a, count_b = Counter(a), Counter(b)

    # make a contain all keys(a may not contain all b's keys)
    for key in count_b.keys():
        if key not in count_a:
            count_a[key] = 0

    diff = []
    for key, item in count_a.items():
        diff.append((key, abs(item - count_b[key])))

    diff = sorted(diff, key=lambda k: k[1], reverse=True)

    return [diff[i][0] for i in range(2)]
