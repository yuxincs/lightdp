import numpy as np
import multiprocessing as mp
import math
import codecs
import os


def _core_hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations):
    # TODO: to remove manual assertions, we should analyze the code and auto-generate the assertions
    # check if input queries are valid
    # assert all(abs(a - b) <= 1 for a, b in zip(D1, D2))
    cx, cy = 0, 0

    for _ in range(iterations):
        cx += 1 if algorithm(D1, *args, **kwargs) in S else 0
        cy += 1 if algorithm(D2, *args, **kwargs) in S else 0

    def test(cx, cy):
        counter = 0
        for i in range(iterations):
            r = np.random.binomial(cx, 1.0 / (np.exp(epsilon)))
            # t = np.random.binomial(cy + r, 0.5)
            t = np.random.hypergeometric(iterations, iterations, cy + r)
            if t >= r:
                counter += 1

        return float(counter) / iterations

    cx, cy = (cx, cy) if cx > cy else (cy, cx)
    return test(cx, cy), test(cy, cx)


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
        return _core_hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations)
    else:
        def process_hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations, result_queue):
            np.random.seed(int(codecs.encode(os.urandom(4), 'hex'), 16))
            result_queue.put(_core_hypothesis_test(algorithm, args, kwargs, D1, D2, S, epsilon, iterations))

        process_count = mp.cpu_count() if cores == 0 else cores
        result_queue = mp.Queue()

        processes = []
        for p_id in range(process_count):
            process_iterations = int(math.floor(float(iterations) / process_count))
            process_iterations += iterations % process_iterations if p_id == process_count - 1 else 0
            process = mp.Process(target=process_hypothesis_test,
                                 args=(algorithm, args, kwargs, D1, D2, S, epsilon, process_iterations, result_queue))
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
