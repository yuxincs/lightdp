"""
This module provides a wrapper for numpy.py which keeps track of the weights for distributions
"""
import numpy.random


def lap(scale):
    return numpy.random.laplace(loc=0.0, scale=scale, size=None)