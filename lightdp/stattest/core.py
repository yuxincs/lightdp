import numpy as np
import multiprocessing as mp
import math
import codecs
import os


def _core_hypothesis_test(algorithm, args, kwargs, eps, D1, D2, S, test_stat, sig_test_stat, iterations):

    # TODO: to remove manual assertions, we should analyze the code and auto-generate the assertions
    # check if input queries are valid
    # assert all(abs(a - b) <= 1 for a, b in zip(D1, D2))

    # compute test statistic T
    x, y = [], []

    for _ in range(iterations):
        a = algorithm(D1, *args, **kwargs)
        b = algorithm(D2, *args, **kwargs)
        if a in S:
            x.append(a)
        if b in S:
            y.append(b)

    T1 = test_stat(x, y, iterations, eps)
    T2 = test_stat(y, x, iterations, eps)

    # compute significance of the value of T
    R = x + y
    ti = [sig_test_stat(R, eps, iterations) for _ in range(iterations)]

    return sum([x >= T1 for x in ti]), sum([x >= T2 for x in ti])


def hypothesis_test(algorithm, args, kwargs, eps, D1, D2, S, test_stat, sig_test_stat, iterations, cores=1):
    """
    :param algorithm: The algorithm to run on
    :param args: The arguments the algorithm needs
    :param D1: Database 1
    :param D2: Databse 2
    :param iterations: Number of iterations to run
    :param test_stat: Statistical test function
    :param sig_test_stat: Significance statistical test function
    :return:
    """
    np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
    if cores == 1:
        sum1, sum2 = _core_hypothesis_test(algorithm, args, kwargs, eps, D1, D2, S,
                                           test_stat, sig_test_stat, iterations)
        return float(sum1) / iterations, float(sum2) / iterations
    else:
        def process_hypothesis_test(algorithm, args, kwargs, eps, D1, D2, S, test_stat, sig_test_stat, iterations, result_queue):
            np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
            result_queue.put(_core_hypothesis_test(algorithm, args, kwargs, eps, D1, D2, S, test_stat, sig_test_stat, iterations))

        process_count = mp.cpu_count() if cores == 0 else cores
        result_queue = mp.Queue()

        processes = []
        for p_id in range(process_count):
            process_iterations = int(math.floor(float(iterations) / process_count))
            process_iterations += iterations % process_iterations if p_id == process_count - 1 else 0
            process = mp.Process(target=process_hypothesis_test,
                                 args=(algorithm, args, kwargs, eps, D1, D2, S, test_stat, sig_test_stat,
                                       process_iterations, result_queue))
            processes.append(process)
            process.start()

        for process in processes:
            process.join()

        total_sum1 = 0
        total_sum2 = 0
        for _ in range(process_count):
            sum1, sum2 = result_queue.get()
            total_sum1 += sum1
            total_sum2 += sum2

        return float(total_sum1) / iterations, float(total_sum2) / iterations



