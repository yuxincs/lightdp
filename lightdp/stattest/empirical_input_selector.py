import numpy as np
import math
import selectors

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






if __name__=='__main__':
    print(database_gene())








