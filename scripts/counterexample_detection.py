import numpy as np
from collections import Counter


# Create two values of input which satisfies the property of input query, along with some hyperparameters
D1=[5.75,4.34,6.15,3.2,6.0,4.6,3.56,6.24,5.86,5.68]
D2=[5.21,3.52,5.57,3.18,6.3,5.1,4.15,5.72,5.99,5.32]
diff=[a-b for a,b in zip(D1,D2)]
eps=2
n=100

def noisymax(Q,eps):
    """
        Here use noisy max algorithm as a test case.
        The noise source will be laplace mechanism.
        Here the largest noise element is returned instead of the index of primal query.

    :param Q: The input query
    :param eps: parameter of lapalce mechanism
    :return: index of maximum value from noisy result
    """

    # add lapalce noise
    N=[a + np.random.laplace(scale=1.0/eps) for a in Q]

    # compare the largest noisy element and return the index of primal query along with the max value
    return np.argmax(N)


def test_stat(x,y):
    """
        Function to compute test statistic T
    :param x: input array
    :param y: input array
    :return: T
    """

    result=(len(x)/n)-(np.exp(eps))*(len(y)/n) # one of the options
    return result

def sig_test_stat(R):
    """
        Function to compute significance of the value of T
    :param R: x and y
    :return: test statistic
    """

    X=[]
    Y=[]
    for i in R:
        if np.exp(eps)/(1+(np.exp(eps))) >= np.random.random():
            X.append(i)
        else:
            Y.append(i)
    return (test_stat(X,Y))

def rev_sig_test_stat(R):
    """
        Function to reverse compute significance of the value of T
    :param R: x and y
    :return: test statistic
    """

    X=[]
    Y=[]
    for i in R:
        if np.exp(eps)/(1+(np.exp(eps))) >= np.random.random():
            X.append(i)
        else:
            Y.append(i)
    return (test_stat(Y,X))

if __name__=="__main__":
    # check if input queries are valid to use
    if all(abs(x)<=1 for x in diff):
        print('Valid Input')
    else:
        print('Invalid Input')

    # to find a reasonable S
    A=[]
    B=[]
    for i in range(100):
        A.append(noisymax(D1,eps))
        B.append(noisymax(D2,eps))
    print(Counter(A+B))

    S=[4,7,8]  # write as {4,7,8} in reports

    # compute test statistic
    x=[]
    y=[]
    for i in range(n):
        a=noisymax(D1,eps)
        b=noisymax(D2,eps)
        if a in S:
            x.append(a)
        if b in S:
            y.append(b)

    T1=test_stat(x,y)
    T2=test_stat(y,x)

    # compute significance of test statistic
    R=x+y
    ti1=[]
    ti2=[]
    for i in range(n):
        ti1.append(sig_test_stat(R))
        ti2.append(rev_sig_test_stat(R))


    print(T1,T2)
    print(ti2)
    # compute p value
    print("p values are "+str(sum([x>=T1 for x in ti1])/n) +" and "+str(sum([x>=T2 for x in ti2])/n))
