import numpy

#neighboring inputs change by 1
# normally prng = numpy.random.RandomState(seed) or numpy.random
#
# in normal operation, this would be called as
# prng = numpy.random.RandomState(seed)
# result = main(eps, x, prng)
#
#in statistical debugging mode, this would be called
# prng = lightdbstat.ImportanceSampler(params go here)
# result = main(eps, x, prng)
# prng.getweight()
def mech(eps, x, prng):
    sigma = numpy.sqrt(2.0)/eps
    return prng.normal(scale=sigma) + x
