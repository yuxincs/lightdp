

def havoc(scale):
    'Implement the havoc instruction here'
    pass

def SparseVector(T, N, len, epsilon, q):
    __V_epsilon = 0
    out = []
    __V_epsilon += (1.0 / (2 / epsilon))
    eta_1 = havoc((2 / epsilon))
    T_threshold = (T + eta_1)
    c1 = 0
    c2 = 0
    i = 0
    while ((c1 < N) and (i < len)):
        __V_epsilon += (1.0 / ((4 * N) / epsilon))
        eta_2 = havoc(((4 * N) / epsilon))
        if ((q[i] + eta_2) >= T_threshold):
            out.append(True)
            c1 = (c1 + 1)
        else:
            out.append(False)
            c2 = (c2 + 1)
        i = (i + 1)
    return (out, __V_epsilon)
