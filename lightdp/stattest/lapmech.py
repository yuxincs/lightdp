#import numpy

#neighboring inputs change by 1
def mech(eps, x, prng):
    return prng.laplace(scale=1/float(eps)) + x
