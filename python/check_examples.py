"""Check the paper's worked formulas using exact arithmetic (standard library only).

This checks exposition against the bundled verifier. It is not a new
independent reconstruction of the Riemann--Roch or orbital algorithms.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import verify_decompositions as v

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run Python with -O.')

root = Path(__file__).resolve().parent
data = json.loads((root / "data/decompositions_certificate.json").read_text())
profiles = [
    [1, 4], [1, 1], [1, 1, 4], [1, 4, 4, 4], [1, 16, 16, 16],
    [1, 1, 1, 1, 4], [1, 16, 16, 16, 16], [1, 1, 1, 1, 4, 4, 16],
    [1] * 7 + [16, 16], [1] * 7 + [4, 16, 16],
    [1] * 9 + [16, 16], [1] * 12 + [4, 16],
]
assert data["profiles"] == profiles
groups = [
    (1, list(range(4, 15, 2)), [0]),
    (2, list(range(6, 15, 2)), [0, 6]),
    (3, list(range(8, 15, 2)), [6, 7, 10]),
    (4, [10, 12], [2, 5, 7, 10, 11]),
    (4, [14], [3, 6, 9, 10, 11]),
    (5, [12, 14], [0, 2, 4, 5, 7, 8, 11]),
    (6, [14], [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11]),
]
assert [(g["k"], g["dimensions"], g["support"]) for g in data["groups"]] == groups

D5 = {(2, 0, 0): F(72), (1, 1, 0): F(536, 45),
      (0, 2, 0): F(4, 9), (0, 0, 1): F(4, 45)}
D6 = {(2, 0, 0): F(96), (1, 1, 0): F(832, 45),
      (0, 2, 0): F(8, 9), (0, 0, 1): F(8, 45)}
assert v.rr_density(5) == D5 and v.rr_density(6) == D6
assert F(8, 45) / 2 + F(32, 45) / 2 == F(4, 9)
assert F(8, 45) / 2 == F(4, 45)
o1 = v.orbital(14, 1, profiles[0], 3)
o3 = v.orbital(14, 3, profiles[0], 3)
assert o1 == {(2, 1, 0, 0): F(5, 203)}
assert o3 == {(0, 3, 0, 0): F(3397, 1749403656),
              (0, 1, 1, 0): F(5967, 1749403656),
              (0, 0, 0, 1): F(2570, 1749403656)}
o20 = v.orbital(14, 2, profiles[0], 2)
o26 = v.orbital(14, 2, profiles[6], 2)
assert o20 == {(0, 2, 0): F(3077, 11044215), (0, 0, 1): F(1837, 11044215)}
assert o26 == {(0, 2, 0): F(111025, 2208843), (0, 0, 1): F(11825, 2208843)}
l0, l6 = F(532321, 2792790), F(2260469, 2792790)
assert l0 + l6 == 1
assert l0 * F(1837, 3077) + l6 * F(473, 4441) == F(1, 5)
worked = {(2, 0, 0): F(96)}
worked = v.add(worked, v.orbital(14, 1, profiles[0], 2), F(168896, 225))
worked = v.add(worked, o20, F(8, 9) * l0 / F(3077, 11044215))
worked = v.add(worked, o26, F(8, 9) * l6 / F(111025, 2208843))
assert worked == D6

# Independent archived separator coordinates, in the paper's power-sum convention.
L = {(1, 1, 1, 1): F(5401916478, 5), (2, 1, 1): F(-10364733603, 5),
     (2, 2): F(26720008371, 2), (3, 1): F(-7067915757, 10),
     (4,): F(68415542937, 20)}
D14 = v.rr_density(14)
target = sum(L[mu] * D14.get(v.exponent(mu, 6), 0) for mu in L)
assert target == -F(54836518701826, 5630625)
eta = {e: 192 * c for e, c in v.add(o1, o3).items()}
eta2 = {e + (0, 0, 0): c for e, c in v.square(eta).items()}
effect = sum(L[mu] * eta2.get(v.exponent(mu, 6), 0) for mu in L)
assert effect / (2 * 192**2) == -F(30055, 203)
assert target - effect == F(192151530447046, 163288125)
# Polynomial identity on all spectral profiles: compare all Schur coordinates.
spectral_square = {(2, 2): F(1), (2, 1, 1): F(-3, 5), (1, 1, 1, 1): F(9, 100)}
from math import factorial, prod
for lam in v.partitions(4):
    kernel = 4**4 * prod(F(factorial(2*(14-i-1)+1),
                             factorial(2*(14-i-1+a)+1)) for i, a in enumerate(lam))
    actual = kernel * sum(F(v.character(lam, mu), v.z(mu)) * L[mu] for mu in L)
    expected = sum(c * v.character(lam, mu) for mu, c in spectral_square.items())
    assert actual == expected
assert [v.rr_density(n)[((n-1)//2,) + (0,)*((n-1)//2)] for n in range(5,15)] == [72,96,128,160,200,240,288,336,392,448]
print(json.dumps({"status": "PASS", "checks": [
    "Printed profiles and support tables agree with the frozen certificate",
    "D5 Gaussian example and D6 two-column reconstruction",
    "Displayed first and third moments of the profile (1,4)",
    "All-profile Schur identity for the quartic separator",
    "Separator target, mixed product, and corrected values",
    "Volume coefficients for dimensions 5 through 14",
]}, indent=2))
