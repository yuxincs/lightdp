def SmartSum(epsilon, M, T, q):
    """
    precondition : forall i (^q[i] >= -1 and ^q[i] <= 1);
    epsilon, M, T : num(0); q : list num(*);
    next, n, i : num(0); sum : num(*); eta_1 : num(-^sum-^q[i]); eta_2 : num(-^q[i])
    """
    out = []
    next = 0
    n = 0
    i = 0
    sum = 0
    while i <= T:
        if i + 1 % M == 0:
            eta_1 = Laplace(1/epsilon)
            n = n + sum + q[i] + eta_1
            next = n
            sum = 0
            out.append(next)
        else:
            eta_2 = Laplace(1/epsilon)
            next = next + q[i] + eta_2
            sum = sum + q[i]
            out.append(next)
        i = i + 1
