"""Literal rational SOS checker, independent of the numerical generator.

Only the Python standard library is used. No floating-point tolerance,
optimizer status, hash, or saved polynomial is accepted as proof.
"""

from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations


PERMS = list(permutations(range(4)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(isinstance(value, (int, str)) and not isinstance(value, bool),
            "rational entries must be integer or string literals")
    return Q(value)


def check_law(weights):
    require(len(weights) == 24, "law must have 24 entries")
    require(all(w >= 0 for w in weights), "negative weight")
    for i in range(4):
        for j in range(4):
            require(sum(w for w, p in zip(weights, PERMS) if p[i] == j) == 6,
                    "law has incorrect marginal")
    require(sum(abs(w - 1) for w in weights) <= 2, "TV radius exceeded")


def positive_pivots(matrix):
    """Positive Schur-complement pivots certify a rational matrix is PD."""
    n = len(matrix)
    require(n > 0 and all(len(row) == n for row in matrix), "nonsquare Gram block")
    require(all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(n)),
            "nonsymmetric Gram block")
    work = [row[:] for row in matrix]
    pivots = []
    for i in range(n):
        pivot = work[i][i]
        require(pivot > 0, "nonpositive Gram pivot")
        pivots.append(pivot)
        for j in range(i + 1, n):
            for k in range(j, n):
                work[j][k] -= work[j][i] * work[i][k] / pivot
                work[k][j] = work[j][k]
    return pivots


def check_certificate(cert, expected_weights=None):
    weights = list(map(rational, cert["weights"]))
    check_law(weights)
    if expected_weights is not None:
        require(weights == expected_weights, "certificate law does not match circuit")
    blocks, factors, matrices = cert["blocks"], cert["E"], cert["K"]
    require(len(blocks) == len(factors) == len(matrices) > 0,
            "mismatched block arrays")
    polynomial = defaultdict(Q)
    pivot_count = 0
    max_denominator = 1
    for block, factor, matrix in zip(blocks, factors, matrices):
        require(all(len(m) == 2 and all(type(v) is int and 0 <= v < 16 for v in m)
                    for m in block), "invalid quadratic monomial")
        e = [[rational(v) for v in row] for row in factor]
        k = [[rational(v) for v in row] for row in matrix]
        n = len(k)
        require(len(e) == len(block) and all(len(row) == n for row in e),
                "invalid factor dimensions")
        pivot_count += len(positive_pivots(k))
        max_denominator = max(max_denominator, *(v.denominator for row in k for v in row))
        # Expand q^T K q, q=E^T m, directly as sparse quadratic polynomials.
        quadratics = []
        for col in range(n):
            q = defaultdict(Q)
            for monomial, row in zip(block, e):
                q[tuple(sorted(monomial))] += row[col]
            quadratics.append({m: c for m, c in q.items() if c})
        for i in range(n):
            for j in range(n):
                if not k[i][j]:
                    continue
                for a, ca in quadratics[i].items():
                    for b, cb in quadratics[j].items():
                        polynomial[tuple(sorted(a + b))] += k[i][j] * ca * cb
    target = defaultdict(Q)
    for a in range(16):
        for b in range(16):
            target[tuple(sorted((a, a, b, b)))] += Q(3, 32)
    for p, w in zip(PERMS, weights):
        target[tuple(4 * i + p[i] for i in range(4))] -= w
    keys = set(polynomial) | set(target)
    require(all(polynomial[m] == target[m] for m in keys),
            "quartic coefficient identity failed")
    return {"coefficient_keys": len(keys), "positive_pivots": pivot_count,
            "max_denominator": max_denominator}


def check_bundle(bundle, records):
    require(bundle["format"] == "r4-quartic-sos-v1", "unknown certificate format")
    require(bundle["permutations"] == [list(p) for p in PERMS],
            "incorrect permutation ordering")
    expected = {}
    for rec in records:
        for sign in rec["signs"]:
            key = (rec["support_mask"], sign)
            require(key not in expected, "duplicate expected circuit")
            expected[key] = [1 + Q(sign * c, rec["positive_mass"])
                             for c in rec["primitive"]]
    certificates = bundle["certificates"]
    keys = [(c["support_mask"], c["orientation"]) for c in certificates]
    require(len(keys) == len(set(keys)) and set(keys) == set(expected),
            "certificate coverage mismatch")
    results = [check_certificate(c, expected[key]) for key, c in zip(keys, certificates)]
    return {"certificates": len(results),
            "positive_pivots": sum(r["positive_pivots"] for r in results),
            "max_denominator": max(r["max_denominator"] for r in results),
            "coefficient_keys": sorted(set(r["coefficient_keys"] for r in results))}
