import numpy

from scipy import stats


class Sampler:

    def __init__(self, base_ditribution = 'laplace'):
        self.weight = 1
        if base_ditribution == 'laplace':
            self.base = stats.laplace
        elif base_ditribution == 'normal':
            self.base = stats.norm
        else:
            self.base = stats.laplace

    def get_weight(self):
        return self.weight

    def set_weight(self, w):
        self.weight = w

    def laplace(self, loc=0.0, scale=1.0):
        r = numpy.random.laplace(loc, scale)
        self.weight *= stats.laplace.pdf(r, loc, scale) / self.base.pdf(r, loc, scale)
        return r

    def normal(self, loc=0.0, scale=1.0):
        r = numpy.random.normal(loc, scale)
        self.weight *= stats.norm.pdf(r, loc, scale) / self.base.pdf(r, loc, scale)
        return r

