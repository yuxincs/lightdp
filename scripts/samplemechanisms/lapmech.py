import numpy

#neighboring inputs change by 1
def mech(eps, x):
    return numpy.random.laplace(scale=1/float(eps)) + x
