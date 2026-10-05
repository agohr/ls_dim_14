"""Independent exact RR and adjacent-density check, using only the stdlib.

The implementation expands a univariate series separately for each Weyl
power-sum monomial. It imports no archived calculation module. Coefficients
are Fractions throughout. Run this file to check scalar terms and adjacent-dimension identities through n=14.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import argparse
import json


def partitions(n, largest=None):
    if n == 0:
        yield ()
        return
    for a in range(min(n, largest or n), 0, -1):
        for tail in partitions(n - a, a):
            yield (a,) + tail


def multiply(a, b, order):
    return [sum((a[j] * b[k-j] for j in range(k+1)
                 if j < len(a) and k-j < len(b)), Q(0))
            for k in range(order+1)]


def exponential(logarithm, order):
    answer = [Q(1)]
    for k in range(1, order+1):
        answer.append(sum((j * logarithm[j] * answer[k-j]
                           for j in range(1, k+1)), Q(0)) / k)
    return answer


@lru_cache(None)
def log_f(order):
    # First invert sinh(sqrt(t)/2)/(sqrt(t)/2); then use f'=f(log f)'.
    denominator = [Q(1, 4**j * factorial(2*j+1))
                   for j in range(order+1)]
    f = [Q(1)]
    for k in range(1, order+1):
        f.append(-sum((denominator[j] * f[k-j]
                       for j in range(1, k+1)), Q(0)))
    logarithm = [Q(0)]
    for k in range(1, order+1):
        logarithm.append(f[k] - sum((Q(j, k) * logarithm[j] * f[k-j]
                                     for j in range(1, k)), Q(0)))
    return tuple(logarithm)


def character(n, order):
    r = n+1 if n % 2 else n+2
    weights = Counter()
    for j in range(r+1):
        for shift in ((-1, 1) if n % 2 else (0,)):
            weights[r-2*j+shift] += (-1)**j * comb(r, j)
    return [sum((Q(c * w**(2*k), factorial(2*k))
                 for w, c in weights.items()), Q(0))
            for k in range(order+1)]


@lru_cache(None)
def reduced_density(n):
    """Return coefficients indexed by partitions of Weyl degree.

    A partition mu represents u^(K-|mu|) times product_j p_mu[j],
    where K=floor((n-1)/2). The omitted common power is u^(n-K).
    """
    degree = (n-1)//2
    ell = log_f(n)
    scalar_log = [Q(0)] + [(2*n+2-4**j)*ell[j]
                           for j in range(1, n+1)]
    scalar = multiply(exponential(scalar_log, n), character(n, n), n)
    a = {j: [2*(-1)**j*comb(2*(j+k), 2*j)*ell[j+k]
             for k in range(n-j+1)] for j in range(1, degree+1)}
    answer = {}
    for weight in range(degree+1):
        for mu in partitions(weight):
            remaining = n-weight
            term = scalar[:remaining+1]
            for j, count in Counter(mu).items():
                for _ in range(count):
                    term = multiply(term, a[j], remaining)
                term = [q / factorial(count) for q in term]
            if term[remaining]:
                answer[mu] = term[remaining]
    return answer


def main():
    if not __debug__:
        raise RuntimeError("Verification requires assertions; do not run Python with -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--maximum', type=int, default=14)
    args = parser.parse_args()
    if args.maximum < 2:
        parser.error('--maximum must be at least 2')
    for n in range(2, args.maximum + 1):
        current = reduced_density(n)
        scalar = 2*(n+1)**2 if n % 2 else 2*n*(n+2)
        assert current[()] == scalar, n
        print(f'PASS: n={n}, exact density with {len(current)} coefficients; scalar {scalar}')
        if n % 2 == 0 and n >= 4:
            middle, previous = reduced_density(n-1), reduced_density(n-2)
            keys = set(current) | set(middle) | set(previous)
            assert all(2*middle.get(mu, 0) == current.get(mu, 0)+previous.get(mu, 0)
                       for mu in keys), ('adjacent mismatch', n)
            print(f'PASS: 2 D_{n-1} = D_{n} + u D_{n-2}')


if __name__ == '__main__':
    main()
