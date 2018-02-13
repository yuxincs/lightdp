def noisymax(epsilon, N, q):
    """
    precondition : forall i (^q[i] >= -1 and ^q[i] <= 1);
    q : list num(*); out : num(*); N : num(0);
    i, bq, cq : num(0); eta : num(-^q[i]); max_num : num(0)
    """
    out = 0
    i = 0
    bq = 0
    cq = 0
    while i < N:
        eta = Laplace(2 / epsilon)
        cq = q[i] + eta
        if cq > bq and i == 1:
            out = i
            bq = cq
        i = i + 1
