from functools import reduce


def gcd(a=0, b=0):
    if isinstance(a, list):
        return gcdList(a)
    if b == 0:
        return a
    else:
        return gcd(b, a % b)


def gcdList(_list=[]):
    return reduce(gcd, _list)
