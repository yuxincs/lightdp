"""
This module provides a wrapper for numpy.py which keeps track of the weights for distributions
"""
import numpy.random
import json

__function_map = {
    'lap': {
        'name': 'laplace',
        'args': {'loc': 0.0, 'size': None}
    }
}

# add another layer for mapping for security
__numpy_map = {
    'laplace': numpy.random.laplace
}


def load_config(config):
    # merge the config into the default function map
    global __function_map
    __function_map = config


def get_config():
    json.dumps(__function_map)


def sample(name):
    config = __function_map.get(name)
    try:
        dist_func = __numpy_map[config.get('name')]
    except KeyError as ex:
        ex.args = ('No numpy functions found. Check your config.', )
        raise

    return lambda scale: dist_func(scale=scale, **config.get('args'))
