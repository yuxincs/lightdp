from inspect import isfunction

def s_selector(algorithm):
    assert isfunction(algorithm)
    if algorithm.__name__ == 'noisymax':
        return [7, 4, 2]
    if algorithm.__name__ == 'sparsevector':
        return [9]