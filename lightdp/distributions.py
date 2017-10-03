"""
This module provides a wrapper for numpy.py which keeps track of the weights for distributions
"""
import numpy.random


def lap(loc, scale, size):
    return numpy.random.laplace(loc, scale, size)