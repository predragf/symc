from functools import reduce
try:
    from collections.abc import Iterable  # noqa
except ImportError:
    from collections import Iterable


def gcd(a=0, b=0):
    if isinstance(a, Iterable):
        return gcdList(a)
    if b == 0:
        return a
    else:
        return gcd(b, a % b)


def gcdList(_list=[]):
    return reduce(gcd, _list)
