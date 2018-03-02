def noisymax(epsilon, N, q):
    """
    precondition : forall i (^q[i] >= -1 and ^q[i] <= 1);
    q : list num(*); out : num(0); N : num(0);
    i, bq, cq : num(0); eta : num(-^q[i]); max_num : num(0)
    """
    out = 0
    i = 0
    bq = 0
    while i < N:
        "bq"
        eta = Laplace(2 / epsilon)
        if q[i] + eta > bq and i == 1:
            out = i
            bq = q[i] + eta
        i = i + 1
