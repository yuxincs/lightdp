import numpy

#neighboring inputs change by at most 1 in exactly one list element. x is a list
def mech(eps, x):
    sigma = 2.0 *numpy.sqrt(2.0)/eps
    y = [a + numpy.random.normal(scale=sigma) for a in x]
    ind = numpy.argmax(y)
    return x[ind] + numpy.random.laplace(scale=2.0/eps)
