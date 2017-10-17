import numpy

#neighboring inputs change by 1
def mech(eps, x):
    sigma = numpy.sqrt(2.0)/eps
    return numpy.random.normal(scale=sigma) + x
