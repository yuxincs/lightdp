from inspect import isfunction
from collections import Counter


def frequency_s_selector(algorithm, args, kwargs, D1, D2, iterations=1000):
    assert isfunction(algorithm)
    a = [algorithm(D1, *args, **kwargs) for _ in range(iterations)]
    b = [algorithm(D2, *args, **kwargs) for _ in range(iterations)]

    countitem = Counter(a + b).most_common(2)

    return [countitem[0][0], countitem[1][0]]


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

    return [diff[i][0] for i in range(1)]
    
    def sd_s_selector(algorithm, args, kwargs, D1, D2, iterations=1000):
    assert isfunction(algorithm)
    a = [algorithm(D1, *args, **kwargs) for _ in range(iterations)]
    b = [algorithm(D2, *args, **kwargs) for _ in range(iterations)]
    c=10

    Scand=list(range(0,len(D1)))
    max=0
    maxi=0

    for i in Scand:
        p=(a.count(i)+c) / (len(a)+c)
        q=(b.count(i)+c) / (len(b)+c)

        if p==0 and q==0:
            sddiff=0
        else:
            sddiff=abs((p-q)/((p*(1-p) + q*(1-q))**(1/2)))

        if max<sddiff:
            max=sddiff
            maxi=i

    return [maxi]
