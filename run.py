from lightdp.stattest import hypothesis_test, simple_generator, fisher_s_selector
from lightdp.stattest.algorithms import *
from intervals import Interval
from math import inf
import time


def draw_graph(xlabel, ylabel, data, title, name):
    markers = ['.', 'o', '^', 'x', '*', '+', 'p']
    import matplotlib.pyplot as plt
    plt.switch_backend('agg')
    plt.ion()
    plt.show()
    assert isinstance(data, dict)
    x = []
    p2 = []

    for i, (epsilon, points) in enumerate(data.items()):
        x = [i[0] for i in points]
        p1 = [i[1] for i in points]
        p2 = [i[2] for i in points]
        plt.plot(x, p1, 'o-', label='p1 $\epsilon = %.1f$' % epsilon, markersize=8, marker=markers[i])
        plt.axvline(x=epsilon, color='black', linestyle='dashed', alpha=0.8, linewidth=0.8)

    plt.plot(x, p2, 'o-', label='p2', markersize=4, marker=markers[6])
    plt.axhline(y=0.05, color='green', linestyle='dashed', alpha=0.8, linewidth=0.8)
    plt.axhline(y=0.01, color='red', linestyle='dashed', alpha=0.8, linewidth=0.8)

    plt.xlabel(xlabel)
    plt.ylabel(ylabel)
    #plt.title(title)
    #lgd = plt.legend(bbox_to_anchor=(0.5, -0.33), loc='lower center', ncol=1)
    #lgd.remove()
    plt.savefig(name, bbox_inches='tight')
    plt.draw()
    plt.pause(0.001)
    plt.gcf().clear()
    return


def main():
    jobs = [
        {
            "algorithm": svt_v6,
            "kwargs": {'T': 1, 'N': 1},
            #"D1": lambda eps: [0, 1],
            #"D2": lambda eps: [1, 0],
            #"D1": lambda eps: [0, 0, 1, 1],
            #"D2": lambda eps: [1, 1, 0, 0],
            "D1": lambda eps: [0,0,0,0,0,1,1,1,1,1],
            "D2": lambda eps: [1,1,1,1,1,0,0,0,0,0],
            "S": lambda: fisher_s_selector(algorithm, (), kwargs, D1, D2, epsilon,
                                           search_space=[[i] for i in range(11)])
        }
    ]
    """
    import time
    start = time.time()
    v1a = simple_generator(noisy_max_v1a, (), {}, 5, [[i] for i in range(5)])
    print('v1a: ' + str(v1a))
    print('time=%f' % (time.time() - start))
    start = time.time()
    v1a = simple_generator(noisy_max_v1b, (), {}, 5, [Interval([-inf, alpha]) for alpha in range(-5, 6)])
    print('v1b: ' + str(v1a))
    print('time=%f' % (time.time() - start))
    start = time.time()
    v1a = simple_generator(noisy_max_v2a, (), {}, 5, [[i] for i in range(5)])
    print('v2a: ' + str(v1a))
    print('time=%f' % (time.time() - start))
    start = time.time()
    v1a = simple_generator(noisy_max_v2b, (), {}, 5, [Interval([-inf, 1 + alpha / 10.0]) for alpha in range(0, 80, 2)])
    print('v2b: ' + str(v1a))
    print('time=%f' % (time.time() - start))
    start = time.time()
    histo = simple_generator(histogram, (), {}, 5, [Interval([1 + alpha / 10.0, inf]) for alpha in range(0, 20, 2)])
    print('histogram: ' + str(histo))
    print('time=%f' % (time.time() - start))
    start = time.time()
    sparse = simple_generator(sparse_vector_v1, (), {'T': 2, 'N': 1}, 10, [Interval([alpha, inf]) for alpha in range(1, 11)])
    print('histogram: ' + str(sparse))
    print('time=%f' % (time.time() - start))
    exit(0)
    """
    # manual data for sparsevector
    results = {}

    start_time = time.time()

    for job in jobs:
        results.clear()
        if True:#job['algorithm'].__name__ == 'histogram':
            algorithm = job['algorithm']
            for algorithm_epsilon in [0.5,1,1.5,2]:
                results[algorithm_epsilon] = []
                for epsilon in [x / 10.0 for x in range(1, 45, 1)]:
                    # algorithm's fixed privacy budget
                    kwargs = {'eps': algorithm_epsilon}
                    kwargs.update(job.get('kwargs', {}))

                    D1 = job['D1'](epsilon)
                    D2 = job['D2'](epsilon)

                    # call s selector to find s
                    S = job['S']()

                    p1, p2 = hypothesis_test(algorithm, (), kwargs, D1, D2, S, epsilon, 500000, cores=0)

                    results[algorithm_epsilon].append((epsilon, p1, p2))
                    print("epsilon: %f, p1 = %f, p2 = %f | S = %s" % (epsilon, p1, p2, S))
                    draw_graph('Test $\epsilon$', 'P Value', results,
                               algorithm.__name__.replace('_', ' ').title(),
                               algorithm.__name__ + '.pdf')

            # print output
            print("%s" % algorithm.__name__)
            print("D1 : %s" % D1)
            print("D2 : %s" % D2)
            print("Time elapsed: %f seconds" % (time.time() - start_time))

if __name__ == '__main__':
    main()
