#!/usr/bin/env python3
"""Exact checks supporting equality and the explicit uniform deficit extension.

This standard-library replay checks the twelve product-equality blocks in every
SOS certificate and independently expands the compact scalar quartic identity.
The surrounding proofs (normalization, circuit convexity, and pair estimates)
are mathematical arguments in the accompanying notes, not numerical searches.
Run: python probes/P0182_permanent_robustness/extensions.py
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


class ExtensionVerificationError(ValueError):
    """An exact extension check failed."""


def _require(condition, message):
    if not condition:
        raise ExtensionVerificationError(message)


def _rank(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((row for row in range(rank, len(rows)) if rows[row][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][column]
        rows[rank] = [value / scale for value in rows[rank]]
        for row in range(rank + 1, len(rows)):
            scale = rows[row][column]
            rows[row] = [a - scale * b for a, b in zip(rows[row], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def _positive_pivots(matrix):
    _require(isinstance(matrix, list) and len(matrix) == 3, "Product Gram shape")
    _require(all(isinstance(row, list) and len(row) == 3 for row in matrix),
             "Product Gram row shape")
    residual = [list(map(Fraction, row)) for row in matrix]
    _require(all(residual[i][j] == residual[j][i] for i in range(3) for j in range(3)),
             "Product Gram symmetry")
    for pivot in range(3):
        value = residual[pivot][pivot]
        _require(value > 0, "Product Gram has a nonpositive exact LDL pivot")
        for row in range(pivot + 1, 3):
            for column in range(row, 3):
                residual[row][column] -= (
                    residual[row][pivot] * residual[pivot][column] / value
                )
                residual[column][row] = residual[row][column]


def _product_label(block):
    """Recognize each literal four-product vector, independent of block order."""
    if not isinstance(block, list) or len(block) != 4:
        return None
    valid = all(
        isinstance(pair, list) and len(pair) == 2
        and all(type(index) is int and 0 <= index < 16 for index in pair)
        for pair in block
    )
    _require(valid, "Quadratic monomial index invalid")
    if all(a // 4 == b // 4 and a != b for a, b in block):
        columns = {tuple(sorted((a % 4, b % 4))) for a, b in block}
        _require(len(columns) == 1 and {a // 4 for a, _ in block} == set(range(4)),
                 "Incomplete same-row product block")
        return ("columns",) + next(iter(columns))
    if all(a % 4 == b % 4 and a != b for a, b in block):
        rows = {tuple(sorted((a // 4, b // 4))) for a, b in block}
        _require(len(rows) == 1 and {a % 4 for a, _ in block} == set(range(4)),
                 "Incomplete same-column product block")
        return ("rows",) + next(iter(rows))
    return None


def check_equality_blocks(certificates):
    """Verify all twelve rank-three equality constraints for every certificate.

    Together with the independently checked SOS identities, positive definite
    K and ker(E^T)=span(1,1,1,1) make each product vector constant at equality.
    """
    _require(isinstance(certificates, list) and certificates, "No certificates")
    required_labels = {
        (kind, first, second)
        for kind in ("rows", "columns")
        for first, second in combinations(range(4), 2)
    }
    total = 0
    for certificate in certificates:
        blocks, bases, grams = (certificate[key] for key in ("blocks", "E", "K"))
        _require(len(blocks) == len(bases) == len(grams) == 31,
                 "Expected 31 matched blocks, bases, and Gram matrices")
        labels = set()
        for block, basis, gram in zip(blocks, bases, grams):
            label = _product_label(block)
            if label is None:
                continue
            _require(label not in labels, "Duplicate product-equality block")
            labels.add(label)
            _require(isinstance(basis, list) and len(basis) == 4
                     and all(isinstance(row, list) and len(row) == 3 for row in basis),
                     "Product basis shape must be 4 by 3")
            exact_basis = [list(map(Fraction, row)) for row in basis]
            _require(all(sum(row[column] for row in exact_basis) == 0
                         for column in range(3)), "Product basis does not kill constants")
            _require(_rank(exact_basis) == 3, "Product basis must have rank three")
            _positive_pivots(gram)
            total += 1
        _require(labels == required_labels, "Missing product-equality labels")
    return {"certificates": len(certificates), "product_blocks": total,
            "positive_product_ldl_pivots": 3 * total}


def _add(*polynomials):
    output = defaultdict(Fraction)
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            output[monomial] += coefficient
    return {monomial: coefficient for monomial, coefficient in output.items() if coefficient}


def _scale(polynomial, factor):
    return {monomial: Fraction(factor) * coefficient
            for monomial, coefficient in polynomial.items() if factor * coefficient}


def _multiply(left, right):
    output = defaultdict(Fraction)
    for left_monomial, left_coefficient in left.items():
        for right_monomial, right_coefficient in right.items():
            monomial = tuple(a + b for a, b in zip(left_monomial, right_monomial))
            output[monomial] += left_coefficient * right_coefficient
    return {monomial: coefficient for monomial, coefficient in output.items() if coefficient}


def _power(polynomial, exponent):
    output = {(0, 0, 0, 0): Fraction(1)}
    for _ in range(exponent):
        output = _multiply(output, polynomial)
    return output


def scalar_identity_polynomials():
    """Expand both sides independently from the displayed four-variable formula.

    p_k=sum_i z_i^k;
    q_i=p_1*z_i-3*z_i^2-(p_1^2-3*p_2)/4;
    r=(z_1*z_2+z_3*z_4,z_1*z_3+z_2*z_4,z_1*z_4+z_2*z_3).

    12*p_4+p_1^2*p_2-7*p_2^2
      =6*sum_{i<j} z_i*z_j*(z_i-z_j)^2
       +2*sum_i q_i^2+sum_{a<b}(r_a-r_b)^2.

    On the nonnegative orthant every summand on the right is nonnegative.
    """
    variables = [{tuple(int(i == j) for j in range(4)): Fraction(1)} for i in range(4)]
    moments = {degree: _add(*(_power(z, degree) for z in variables))
               for degree in (1, 2, 4)}
    left = _add(
        _scale(moments[4], 12),
        _multiply(_power(moments[1], 2), moments[2]),
        _scale(_power(moments[2], 2), -7),
    )
    common = _scale(_add(_power(moments[1], 2), _scale(moments[2], -3)), Fraction(1, 4))
    q = [_add(_multiply(moments[1], z), _scale(_power(z, 2), -3), _scale(common, -1))
         for z in variables]
    r = [_add(_multiply(variables[a], variables[b]), _multiply(variables[c], variables[d]))
         for a, b, c, d in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2))]
    weighted_squares = [
        _scale(_multiply(_multiply(variables[i], variables[j]),
                         _power(_add(variables[i], _scale(variables[j], -1)), 2)), 6)
        for i, j in combinations(range(4), 2)
    ]
    right = _add(
        *weighted_squares,
        *(_scale(_power(value, 2), 2) for value in q),
        *(_power(_add(r[i], _scale(r[j], -1)), 2) for i, j in combinations(range(3), 2)),
    )
    return left, right


def check_scalar_identity(left=None, right=None):
    if left is None or right is None:
        left, right = scalar_identity_polynomials()
    _require(not _add(left, _scale(right, -1)), "Scalar quartic identity coefficient mismatch")
    _require(all(sum(monomial) == 4 for monomial in set(left) | set(right)),
             "Scalar identity is not homogeneous of degree four")
    return {"scalar_identity_coefficients": len(set(left) | set(right)),
            "nonnegative_weighted_squares": 6, "ordinary_squares": 7}


def run_checks(path=None, *, negative_controls=True):
    path = Path(path) if path else Path(__file__).with_name("certificates.json")
    bundle = json.loads(path.read_text())
    _require(bundle.get("format") == "r4-quartic-sos-v1", "Certificate format")
    certificates = bundle["certificates"]
    result = {"status": "PASS", **check_equality_blocks(certificates), **check_scalar_identity()}
    if negative_controls:
        corrupted = deepcopy(certificates[0])
        product_index = next(index for index, block in enumerate(corrupted["blocks"])
                             if _product_label(block) is not None)
        value = Fraction(corrupted["E"][product_index][0][0])
        corrupted["E"][product_index][0][0] = str(value + 1)
        try:
            check_equality_blocks([corrupted])
        except ExtensionVerificationError:
            pass
        else:
            raise ExtensionVerificationError("Corrupted product kernel was accepted")
        left, right = scalar_identity_polynomials()
        left[(4, 0, 0, 0)] = left.get((4, 0, 0, 0), Fraction(0)) + 1
        try:
            check_scalar_identity(left, right)
        except ExtensionVerificationError:
            pass
        else:
            raise ExtensionVerificationError("Corrupted scalar identity was accepted")
        result["negative_controls_rejected"] = 2
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path)
    args = parser.parse_args()
    print(json.dumps(run_checks(args.certificates), sort_keys=True))


if __name__ == "__main__":
    main()
