import multiprocessing as mp
import math
from noisymax import noisymax
from sparsevector import sparsevector
from s_selector import s_selector
from test_stat import test_stat
from sig_test_stat import sig_test_stat
import matplotlib.pyplot as plt
import numpy as np
import time
from graph_gene import graph_gene

SD1 = [9.917370926052758, 10.295232500311627, 10.979253058964114, 10.954906274017656,
      9.205904120344211, 10.52166922332997, 9.17760719515679, 9.830086654150426, 9.544008376222147, 10.034087353065718]

SD2 = [9.91737, 10.0, 10.0, 10.31766, 8.39766, 9.62791, 9.99999, 10.48255, 9.99999, 9.86943]

ND1 = [5.75, 4.34, 6.15, 3.2, 5.8, 4.6, 3.56, 6.24, 5.86, 5.68]
ND2 = [5.21, 3.52, 5.57, 3.18, 5.6, 5.1, 4.15, 5.72, 5.99, 5.32]

n=5000
eps2=2
cores=0
c=1
option=2

def to_parallel(algo,D1,D2,eps1,n,result_queue):
    # check if input queries are valid

    assert all(abs(a - b) <= 1 for a, b in zip(D1, D2))

    # choose an S
    S = s_selector(algo, D1, D2, eps1)

    # compute test statistic T
    x,y=[],[]

    for i in range(n):
        a = algo(D1, eps1)
        b = algo(D2, eps1)
        if a in S:
            x.append(a)
        if b in S:
            y.append(b)

    T1 = test_stat(x, y, n,eps2,option,c)
    T2 = test_stat(y, x, n,eps2,option,c)

    # compute significance of the value of T
    R=x+y
    ti=[sig_test_stat(R,eps2,n,option,c) for _ in range(n)]

    result_queue.put((eps1, (sum([x >= T1 for x in ti]) / n), (sum([x >= T2 for x in ti]) / n)))

    return

def hypothesis_test(algo,D1,D2,eps1,n):

    # make compiling parallel
    process_count = mp.cpu_count() if cores == 0 else cores
    result_queue = mp.Queue()
    processes = []

    for p_id in range(process_count):
        process_iterations = int(math.floor(float(n) / process_count))
        process_iterations += n % process_iterations if p_id == process_count - 1 else 0
        process = mp.Process(target=to_parallel, args=(algo, D1, D2, eps1,n,result_queue))
        processes.append(process)
        process.start()

    for process in processes:
        process.join()

    for _ in range(process_count):
        value1, value2, value3= result_queue.get()

    return [value1,value2,value3]

if __name__=="__main__":
    print("sparsevector T option 1")

    result=[]
    for eps1 in np.arange(3,10):
        a = [0, 0, 0]
        for _ in range(1):
            k=hypothesis_test(sparsevector,SD1,SD2,eps1,n)
            a=np.add(k,a)
        result.append([x for x in a])

    print(result)

    graph_gene('eps1','p value',result,'sparsevector with T option 1','sv_T1.png')