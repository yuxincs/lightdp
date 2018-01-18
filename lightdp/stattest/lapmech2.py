import numpy

#neighboring inputs change by 1
def mech(eps, x, fudge=2.0):
    return numpy.random.laplace(scale=1/float(fudge * eps)) + x
