import numpy

#neighboring inputs change by at most 1 in exactly one list element. x is a list
def mech(eps, x, prng):
    y = [a + prng.laplace(scale=2.0/eps) for a in x]
    ind = numpy.argmax(y)
    return x[ind] + prng.laplace(scale=2.0/eps)
