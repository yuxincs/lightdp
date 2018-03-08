import numpy as np
import multiprocessing as mp
import math
import codecs
import os
from scipy import stats


def test_statistics(cx, cy, epsilon, iterations):
    """ old test method
    counter = 0
    for i in range(iterations):
        r = np.random.binomial(cx, 1.0 / (np.exp(epsilon)))
        t = np.random.binomial(cy + r, 0.5)
        if t >= r:
            counter += 1

    return counter
    """
    cx_prime = np.random.binomial(cx, 1.0 / (np.exp(epsilon)))
    return 1 - stats.hypergeom.cdf(cx_prime, 2 * iterations, iterations, cx_prime + cy)


def _run_algorithm(algorithm, args, kwargs, D1, D2, S, iterations):
    cx = sum(1 for _ in range(iterations) if algorithm(D1, *args, **kwargs) in S)
    cy = sum(1 for _ in range(iterations) if algorithm(D2, *args, **kwargs) in S)

    return cx, cy


def _multiprocessing_run(func, args, iterations, process_count):
    def process_func(function, args, kwargs, result_queue):
        np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
        result_queue.put(function(*args, **kwargs))

    result_queue = mp.Queue()

    processes = []
    for p_id in range(process_count):
        process_iterations = int(math.floor(float(iterations) / process_count))
        process_iterations += iterations % process_iterations if p_id == process_count - 1 else 0
        process = mp.Process(target=process_func, args=(func, args, {'iterations': process_iterations}, result_queue))
        processes.append(process)
        process.start()

    for process in processes:
        process.join()

    return (result_queue.get() for _ in range(process_count))


def hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations, cores=1):
    """
    :param algorithm: The algorithm to run on
    :param args: The arguments the algorithm needs
    :param kwargs: The keyword arguments the algorithm needs
    :param D1: Database 1
    :param D2: Database 2
    :param S: The S set
    :param iterations: Number of iterations to run
    :param epsilon: The epsilon value to test for
    :param cores: Number of processes to run, default is 1 and 0 means utilizing all cores.
    :return: (p1, p2)
    """
    np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
    if cores == 1:
        cx, cy = _run_algorithm(algorithm, args, kwargs, D1, D2, S, iterations)
        cx, cy = (cx, cy) if cx > cy else (cy, cx)
        return test_statistics(cx, cy, epsilon, iterations), test_statistics(cy, cx, epsilon, iterations)
    else:
        process_count = mp.cpu_count() if cores == 0 else cores

        result = _multiprocessing_run(_run_algorithm, (algorithm, args, kwargs, D1, D2, S), iterations, process_count)

        cx, cy = 0, 0
        for process_cx, process_cy in result:
            cx += process_cx
            cy += process_cy

        cx, cy = (cx, cy) if cx > cy else (cy, cx)
        return test_statistics(cx, cy, epsilon, iterations), test_statistics(cy, cx, epsilon, iterations)
