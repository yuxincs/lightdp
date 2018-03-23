import numpy as np
import math
from selectors import fisher_s_selector
from core import hypothesis_test

def database_gene(maxlen=8):
    """
    :param maxlen: maximum length of D1 and D2
    :return: database of candidates

    implement empirical D1 and D2 generation, 8 methods in total
     """
    database=[]
    currentlen=1
    while currentlen<=maxlen:
        d1 = [1] * currentlen
        d2=[]

        # one above
        carrier=d1[:]
        carrier[0]=carrier[0]+1
        d2.append(carrier)

        # one below
        carrier = d1[:]
        carrier[0] = carrier[0]-1
        d2.append(carrier)

        # one above rest below
        carrier=[x-1 for x in d1]
        carrier[0]=carrier[0]+2
        d2.append(carrier)

        # one below rest above
        carrier= [x + 1 for x in d1]
        carrier[0] = carrier[0] - 2
        d2.append(carrier)

        # half half gt
        d2.append([x+1 for x in d1][:int(len(d1)/2)]+[x-1 for x in d1][int(len(d1)/2):])

        # half half lt
        d2.append([x-1 for x in d1][:int(len(d1) / 2)] + [x + 1 for x in d1][int(len(d1) / 2):])

        # all above
        d2.append([x+1 for x in d1])

        # all below
        d2.append([x-1 for x in d1])

        d2=[list(tupl) for tupl in {tuple(item) for item in d2 }]

        currentlen=currentlen*2

        for item in d2:
            database.append([d1,item])

    return database

def empi_eval(algorithm, args, kwargs, D1, D2, S, epsilon, iterations):
    algo_eps=1
    database=database_gene()
    result=[]
    c=1
    for comb in database:
        D1=comb[0]
        D2=comb[1]
        eps1, eps2, counter = 0
        for test_eps in np.arange(0.2,algo_eps+0.5,0.1):
            # TODO: need modification
            S=fisher_s_selector(algorithm, (), kwargs, D1, D2, epsilon,
                                           search_space=[[i] for i in range(5)])
            kwargs = {'eps': test_eps}
            p1,p2=hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations)
            if p1!=0 and eps1==0:
                eps1=p1
            if p1>0.98:
                counter+=1
            if counter>=3:
                eps2=p1
                result.append((eps2-eps1)*c/eps1)
                break

    return database(np.argmin(result))



