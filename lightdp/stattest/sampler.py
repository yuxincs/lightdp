import numpy
from scipy import stats


def get_rng(rng):
    if rng == 'laplace':
        return numpy.random.laplace
    elif rng == 'normal':
        return numpy.random.normal
    else:
        raise ValueError('Unknown distribution')


def get_pdf(rng):
    if rng == 'laplace':
        return stats.laplace.pdf
    elif rng == 'normal':
        return stats.norm.pdf
    else:
        raise ValueError('Unknown distribution')


class Sampler:
    def __init__(self, config='laplace'):
        try:
            self.rng = get_rng(config)
            self.pdf = get_pdf(config)
        except ValueError as err:
            print(err.args)
            exit(1)
        self._weight = 1
        self.mu = lambda x: x
        self.sigma = lambda x: x

    def weight(self):
        return self._weight

    def add_config(self, new, f=lambda x: x, g=lambda x: x):
        self.rng = get_rng(new)
        self.pdf = get_pdf(new)
        self.mu = f
        self.sigma = g

    def laplace(self, loc=0.0, scale=1.0):
        m = self.mu(loc)
        s = self.sigma(scale)
        r = self.rng(m, s)
        self._weight *= stats.laplace.pdf(r, m, s) / self.pdf(r, m, s)
        return r

    def normal(self, loc=0.0, scale=1.0):
        m = self.mu(loc)
        s = self.sigma(scale)
        r = self.rng(m, s)
        self._weight *= stats.norm.pdf(r, m, s) / self.pdf(r, m, s)
        return r
