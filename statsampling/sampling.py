import numpy
from scipy import stats

base_pdf = stats.laplace.pdf # TODO: change it to read from a file

weight = 1


def init():
    global weight
    weight = 1


def get_weight():
    return weight


def set_weight(w):
    global weight
    weight = w


def laplace(loc = 0.0, scale = 1.0, size = None):
    r = numpy.random.laplace(loc, scale, size)
    global weight
    weight = weight * stats.laplace.pdf(r, loc, scale) / base_pdf(r, loc, scale)
    return r


def norm(loc = 0.0, scale = 1.0, size = None):
    r = numpy.random.normal(loc, scale, size)
    global weight
    weight = weight * stats.norm.pdf(r, loc, scale) / base_pdf(r, loc, scale)
    return r


# Test

laplace(4, 6)

norm(2, 5)

norm(3, 5)

# init()

set_weight(2)

print(get_weight())

init()

norm()

print(get_weight())

print(stats.norm.cdf(0, 1, 1))



