import numpy
from scipy import stats


class LightdpStat:

    def __init__(self):
        self.weight = 1
        self.base_distr = stats.laplace

    def get_weight(self):
        return self.weight

    def set_weight(self, w):
        self.weight = w

    def laplace(self, eps, x):
        s = 1/float(eps)
        rng = numpy.random.laplace(scale=s) + x
        self.weight *= stats.laplace.pdf(rng, 0, s) / self.base_distr.pdf(rng, 0, s)
        return rng

    def norm(self, eps, x):
        s = 1/float(eps)
        rng = numpy.random.normal(scale = s) + x
        self.weight *= stats.norm.pdf(rng, 0, s) / self.base_distr.pdf(rng, 0, s)
        return rng




# Test
