import numpy
from scipy import stats

base_pdf = stats.laplace.pdf

weight = 1


def get_weight():
    return weight

def init():
    global weight
    weight = 1


def laplace(loc = 0.0, scale = 1.0, size = None):
    r = numpy.random.laplace(loc, scale, size)
    global weight
    weight = weight * stats.laplace.pdf(r) / base_pdf(r)
    return r


def norm(loc = 0.0, scale = 1.0, size = None):
    r = numpy.random.normal(loc, scale, size)
    global weight
    weight = weight * stats.norm.pdf(r) / base_pdf(r)
    return r


# Test

laplace()

norm()

norm()

init()

print(get_weight())

init()

norm()

print(get_weight())

print(stats.norm.pdf(0))



