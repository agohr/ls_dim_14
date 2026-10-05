#!/usr/bin/env python3
"""Independent exact arithmetic, using only Python's standard library.

No geometric assertion is proved by this program. All polynomial arithmetic
uses Fraction. Monomials are tuples of power-sum indices, e.g. (1,1,2).
Run from any directory; --write records the reproducible data and report.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from math import comb, factorial, prod
from pathlib import Path
import argparse
import json


class P(dict):
    def __init__(self, value=0):
        if isinstance(value, dict):
            super().__init__({m: Q(c) for m, c in value.items() if c})
        else:
            super().__init__({(): Q(value)} if value else {})

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = dict(self)
        for m, c in other.items():
            result[m] = result.get(m, Q(0)) + c
        return P(result)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.items()})

    def __sub__(self, other):
        return self + -P(other)

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = {}
        for a, c in self.items():
            for b, d in other.items():
                m = tuple(sorted(a + b))
                result[m] = result.get(m, Q(0)) + c * d
        return P(result)

    __rmul__ = __mul__

    def __truediv__(self, c):
        return self * (1 / Q(c))

    def __pow__(self, k):
        assert k >= 0
        result = P(1)
        for _ in range(k):
            result = result * self
        return result

    def weight(self, k):
        return P({m: c for m, c in self.items() if sum(m) == k})

    def evaluate(self, sums):
        return sum((c * prod(sums[j] for j in m) for m, c in self.items()), Q(0))


def power(j):
    return P({(j,): 1})


@lru_cache(None)
def partitions(k, bound=None):
    if k == 0:
        return ((),)
    return tuple((j,) + tail for j in range(min(k, bound or k), 0, -1)
                 for tail in partitions(k - j, j))


@lru_cache(None)
def bernoulli(k):
    if k == 0:
        return Q(1)
    return -sum(Q(comb(k + 1, j)) * bernoulli(j) for j in range(k)) / (k + 1)


def ell(j):
    return -bernoulli(2 * j) / (2 * j * factorial(2 * j))


def exponential(logs, k):
    values = [P(1)]
    for j in range(1, k + 1):
        values.append(sum((v * logs[v] * values[j-v] for v in range(1, j+1)), P()) / j)
    return values


@lru_cache(None)
def schur(lam):
    k, length = sum(lam), len(lam)
    h = exponential({j: power(j) / j for j in range(1, k+1)}, k)
    result = P()
    for perm in permutations(range(length)):
        term = P((-1) ** sum(perm[i] > perm[j] for i in range(length) for j in range(i+1, length)))
        for i in range(length):
            degree = lam[i] - i + perm[i]
            term *= h[degree] if 0 <= degree <= k else P()
        result += term
    return result


def schur_ones(lam, rank):
    return schur(lam).evaluate({j: Q(rank) for j in range(1, sum(lam)+1)})


def symmetric_dimension(lam):
    hooks = [lam[i] - j + sum(row > j for row in lam[i+1:])
             for i in range(len(lam)) for j in range(lam[i])]
    return Q(factorial(sum(lam)), prod(hooks))


def projection(n, k, rank):
    r = 2 * n + 2
    assert 1 <= rank <= r
    # z_j=2p_j; this is a substitution on power sums, not on eigenvalues.
    result = P()
    for lam in partitions(k):
        if len(lam) <= r:
            coefficient = symmetric_dimension(lam) * schur_ones(lam, rank) / schur_ones(lam, r)
            result += coefficient * P({m: c * 2 ** len(m) for m, c in schur(lam).items()})
    return result


def orbital(n, k, spectrum=None):
    # With spectrum=None retain a second, symbolic power-sum alphabet.
    result = P()
    for lam in partitions(k):
        if len(lam) > n:
            continue
        rho = prod(Q(factorial(2*(n-i)+1), factorial(2*(lam[i-1]+n-i)+1))
                   for i in range(1, len(lam)+1))
        if spectrum is None:
            yield lam, 4**k * rho, schur(lam)
        else:
            sums = {j: sum(Q(a)**j for a in spectrum) for j in range(1, k+1)}
            result += 4**k * rho * schur(lam).evaluate(sums) * schur(lam)
    if spectrum is not None:
        yield result


def O(n, k, spectrum):
    return next(orbital(n, k, spectrum))


def gaussian(k):
    return exponential({j: 2 * (-1)**j * ell(j) * power(j) for j in range(1, k+1)}, k)[k]


def density(n):
    start = n // 2 + 1
    max_j = n - start
    logs = {j: 2 * ell(j) * (P(n+1-2**(2*j-1)) +
            sum(((-1)**v * comb(2*j, 2*v) * power(v) for v in range(1, j+1)), P()))
            for j in range(1, max_j+1)}
    a = exponential(logs, max_j)
    # Character expansion in exponentials is independent of hyperbolic series code.
    degree = 2 * start
    weights = {}
    for i in range(degree+1):
        for shift in ((-1, 1) if n % 2 else (0,)):
            weight = degree - 2*i + shift
            weights[weight] = weights.get(weight, 0) + (-1)**i * comb(degree, i)
    w = {q: sum(Q(c * t**(2*q), factorial(2*q)) for t, c in weights.items())
         for q in range(n+1)}
    assert all(w[q] == 0 for q in range(start))
    return sum((w[n-j] * a[j] for j in range(max_j+1)), P())


# Printed certificate entries (weight, rank, rational coefficient).
TABLES = {
 5: (72, [(1,12,Q(268,45)),(2,12,Q(3,45)),(2,1,Q(312,45))]),
 6: (96, [(1,14,Q(416,45)),(2,14,Q(6,45)),(2,1,Q(840,45))]),
 7: (128, [(1,16,Q(28080,1890)),(2,16,Q(668,1890)),(2,1,Q(100096,1890)),
           (3,16,Q(3,1890)),(3,1,Q(6528,1890)),(3,2,Q(4080,1890))]),
 8: (160, [(1,18,Q(96720,4725)),(2,18,Q(2710,4725)),(2,1,Q(485640,4725)),
           (3,18,Q(15,4725)),(3,1,Q(43320,4725)),(3,2,Q(29070,4725))]),
 9: (200, [(1,1,Q(180512,315)),(2,1,Q(8752,45)),(2,20,Q(14704,14175)),
           (3,1,Q(2992,405)),(3,2,Q(2090,81)),(3,20,Q(239,28350))]),
 10: (240, [(1,1,Q(182336,225)),(2,1,Q(1495736,4725)),(2,22,Q(21278,14175)),
            (3,1,Q(4048,4725)),(3,2,Q(23276,405)),(3,22,Q(194,14175))]),
 11: (288, [(1,24,Q(2482652,51975)),(2,1,Q(3094720,6237)),(2,24,Q(214814,93555)),
            (3,2,Q(164360,2673)),(3,3,Q(10048,891)),(3,4,Q(922051,93555))]),
 12: (336, [(1,26,Q(3050776,51975)),(2,1,Q(12506936,17325)),(2,26,Q(1445966,467775)),
            (3,1,Q(472784,155925)),(3,2,Q(152711,18711)),(3,3,Q(1771432,18711))]),
}
ORBITALS = {
 11: [((1,1), Q(1008851484437,2142693)), ((2,1,1),Q(151204920425,714231)),
      ((5,1,1,1,1),Q(10770035384,714231)), ((10,)+(1,)*8,Q(51654964,6428079)),
      ((10,)+(1,)*10,Q(252882056,1530495))],
 12: [((1,1),Q(2298362246,9933)), ((1,1,1),Q(194400388184,148995)),
      ((2,1,1),Q(7327263802,9933)), ((10,)+(1,)*8,Q(178334456,148995)),
      ((10,)+(1,)*9,Q(4485216,3311))],
}


def encode(p):
    return [{"powers": list(m), "coefficient": str(c)} for m, c in sorted(p.items())]


def run():
    if not __debug__:
        raise RuntimeError("Verification requires assertions; do not run Python with -O.")
    report = []
    densities = {n: density(n) for n in range(2,15)}
    for n, p in densities.items():
        scalar = 2*n*(n+2) if n % 2 == 0 else 2*(n+1)**2
        assert p.get((), 0) == scalar, (n, "scalar")
        assert max(map(sum, p)) == (n-1)//2
    report.append("PASS: scalar reserves and maximum Weyl weights, n=2..14")
    for n, (constant, entries) in TABLES.items():
        assert all(c > 0 for _, _, c in entries)
        rhs = P(constant) + sum((c * projection(n,k,r) for k,r,c in entries), P())
        if n in (9,10):
            rhs += 2**(n+2) * gaussian(4)
        if n in (11,12):
            assert all(c > 0 and len(a) <= n and all(x >= 0 for x in a) for a,c in ORBITALS[n])
            rhs += sum((c*O(n,4,a) for a,c in ORBITALS[n]), P())
            rhs += 2**(n+2) * gaussian(5)
        assert densities[n] == rhs, (n, encode(densities[n]-rhs))
        report.append(f"PASS: full printed certificate n={n}, exact polynomial equality and positive coefficients")
    basis = [(1,1,1,1),(1,1,2),(2,2),(1,3),(4,)]
    for n, vector, a, denominator in [
        (13,[32231,-53169,301931,-19969,81681],3,221130),
        (14,[33248,-94256,878742,-28008,227741],4,246645)]:
        functional = lambda p: sum(v*p.get(m,0) for v,m in zip(vector,basis))
        lhs = sum((rho * functional(s) * schur(lam) for lam,rho,s in orbital(n,4)), P())
        assert lhs == (a*power(2)-power(1)**2)**2 / denominator
        target = functional(densities[n].weight(4))
        assert target < 0
        report.append(f"PASS: symbolic orbital separator n={n}; target value {target}")
    for n, vector, expected in [
        (11,[2695,-4585,25339,-1295,4361],Q(-67336,93555)),
        (12,[15138,-26651,150977,-6873,23971],Q(-245414,17325))]:
        assert sum(v*densities[n].get(m,0) for v,m in zip(vector,basis)) == expected
    report.append("PASS: n=11,12 PSD separator target values (not its universal generator formula)")
    from verify_h2 import check_witness
    for h2_n in (13, 14):
        h2_path = Path(__file__).resolve().parent / "data" / f"h2_witness_n{h2_n}.json"
        h2_dimension, h2_orbitals, h2_squares, h2_coordinates = check_witness(h2_path)
        assert h2_dimension == h2_n and h2_coordinates == 30
        report.append(f"PASS: full n={h2_n} H2 rational polynomial identity, {h2_orbitals} positive orbital terms and {h2_squares} positive square, with all u powers")
    report.append("NOT PROVED: geometric input theorems, orbital integral interpretation, Hodge-square positivity, classification")
    data = {"schema": "powers lists power-sum indices; restore u^(n-sum(powers)); exact rational strings",
            "densities": {str(n): encode(p) for n,p in densities.items()},
            "projection_certificates": {str(n): {"scalar": str(c), "terms": [
                {"weight": k,"rank":r,"coefficient":str(v)} for k,r,v in terms]}
                for n,(c,terms) in TABLES.items()},
            "gaussian_certificates": {str(n): {"weight": 4 if n <= 10 else 5,
                "coefficient": str(2**(n+2))} for n in range(9,13)},
            "orbital_certificates": {str(n): [{"spectrum":a,"coefficient":str(c)} for a,c in terms]
                                     for n,terms in ORBITALS.items()}}
    return data, "\n".join(report) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data, report = run()
    if args.write:
        root = Path(__file__).resolve().parent
        (root / "results").mkdir(exist_ok=True)
        (root / "results" / "exact_coefficients.json").write_text(json.dumps(data, indent=2) + "\n")
        (root / "results" / "VERIFICATION.txt").write_text(report)
    print(report, end="")
