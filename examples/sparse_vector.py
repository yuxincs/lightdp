def SparseVector(T, N, len, epsilon, q):
    """
    precondition : forall i (^q[i] >= -1 and ^q[i] <= 1);
    T, N, len, epsilon : num(0); q : list num(*); out : list bool;
    c1, c2, i : num(0); T_threshold, eta_1 : num(1); eta_2 : num(2 if q[i] + eta_2 >= T_threshold else 0)
    """
    out = []
    eta_1 = Laplace(2 / epsilon)
    T_threshold = T + eta_1
    c1 = 0
    c2 = 0
    i = 0
    while c1 < N and i < len:
        eta_2 = Laplace(4 * N/epsilon)
        if q[i] + eta_2 >= T_threshold:
            out.append(True)
            c1 = c1 + 1
        else:
            out.append(False)
            c2 = c2 + 1
        i = i + 1
    return out
