#!/usr/bin/env python3
"""Check supplied H2 coefficient witnesses with exact rational arithmetic.

This is a witness *verifier*, not the floating-point search used to discover a
witness. It independently reconstructs the index density and every orbital
polynomial through verify.py and compares the full u-homogeneous polynomial.
It proves no analytic orbital interpretation or Hodge-square positivity.
"""

from fractions import Fraction
from pathlib import Path
import json

import verify


def add(left, right):
    result = dict(left)
    for key, coefficient in right.items():
        result[key] = result.get(key, Fraction(0)) + coefficient
        if result[key] == 0:
            del result[key]
    return result


def multiply(left, right):
    result = {}
    for (u_left, p_left), c_left in left.items():
        for (u_right, p_right), c_right in right.items():
            key = (u_left + u_right, tuple(sorted(p_left + p_right)))
            result[key] = result.get(key, Fraction(0)) + c_left * c_right
    return {key: coefficient for key, coefficient in result.items() if coefficient}


def scale(poly, coefficient):
    return {key: coefficient * value for key, value in poly.items() if value}


def shift_u(poly, exponent):
    assert exponent >= 0
    return {(u + exponent, powers): coefficient
            for (u, powers), coefficient in poly.items()}


def homogenize(poly, total_weight):
    result = {}
    for powers, coefficient in poly.items():
        u_power = total_weight - sum(powers)
        assert u_power >= 0, (total_weight, powers)
        result[(u_power, powers)] = coefficient
    return result


def factor_poly(entry):
    weight = entry["weight"]
    assert isinstance(weight, int) and weight >= 0
    powers = entry["factor"]["powers"]
    coefficients = entry["factor"]["coefficients"]
    assert len(powers) == len(coefficients)
    result = {}
    for indices, raw_coefficient in zip(powers, coefficients):
        assert all(isinstance(j, int) and j > 0 for j in indices)
        monomial = tuple(sorted(indices))
        u_power = weight - sum(monomial)
        assert u_power >= 0
        key = (u_power, monomial)
        assert key not in result
        result[key] = Fraction(raw_coefficient)
    assert result
    return result


def check_witness(path):
    path = Path(path)
    data = json.loads(path.read_text())
    dimension = data["dimension"]
    assert dimension in (13, 14)
    scalar = Fraction(data["scalar"])
    assert scalar > 0
    rhs = {(dimension, ()): scalar}

    squares = data.get("squares", [data["square"]] if "square" in data else [])
    assert squares
    for entry in squares:
        coefficient = Fraction(entry["coefficient"])
        assert coefficient > 0
        weight = entry["weight"]
        assert 2 * weight <= dimension
        factor = factor_poly(entry)
        square = scale(shift_u(multiply(factor, factor), dimension - 2 * weight),
                       coefficient)
        rhs = add(rhs, square)

    terms = data["orbital_terms"]
    assert terms
    for entry in terms:
        k = entry["weight"]
        assert isinstance(k, int) and 1 <= k <= dimension
        spectrum = entry["spectrum"]
        assert 1 <= len(spectrum) <= dimension
        assert all(isinstance(a, int) and a >= 0 for a in spectrum)
        assert any(a > 0 for a in spectrum)
        coefficient = Fraction(entry["coefficient"])
        assert coefficient > 0
        orbital = verify.O(dimension, k, spectrum)
        assert orbital == orbital.weight(k)
        rhs = add(rhs, scale(homogenize(orbital, dimension), coefficient))

    target = homogenize(verify.density(dimension), dimension)
    assert rhs == target, (dimension, len(add(rhs, scale(target, -1))))
    assert all(u + sum(powers) == dimension for u, powers in rhs)
    return dimension, len(terms), len(squares), len(target)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Verification requires assertions; do not run Python with -O.")
    data_dir = Path(__file__).resolve().parent / "data"
    for dimension in (13, 14):
        path = data_dir / f"h2_witness_n{dimension}.json"
        if path.exists():
            n, orbital_count, square_count, coordinate_count = check_witness(path)
            square_label = "square" if square_count == 1 else "squares"
            print(f"PASS: n={n} H2 full u-homogeneous rational identity; "
                  f"{orbital_count} positive orbital terms, {square_count} positive {square_label}, "
                  f"{coordinate_count} coordinates")
        else:
            raise FileNotFoundError(f"Required witness is absent: {path}")
