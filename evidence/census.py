"""Complete exact circuit census for the four-row permutation incidence matrix.

The columns are the 24 permutations in lexicographic order.  A circuit is a
support-minimal nonzero vector in their kernel.  The default replay uses only
the Python standard library; no floating-point calculations occur.

Completeness proof.  Keep every orbit of independent column subsets, starting
with the empty set.  Extend each representative by every missing column and
canonicalize using all 576 independent row and column relabelings.  Every
independent set is reached by deleting one column and applying this induction.
Every circuit is reached by deleting any one of its columns.  A dependent
extension of an independent set has a one-dimensional kernel; it is a circuit
exactly when that kernel vector has no zero coordinate.  Dependent sets need
not be extended.  Rank is ten, so no circuit has more than eleven columns.

Rank is tested modulo PRIME=65521.  The rational rank of the full matrix is
independently calculated as ten.  Each original incidence column has Euclidean
norm two.  Hadamard's inequality bounds every minor of order at most ten by
2**10=1024 < PRIME.  Thus a rationally nonzero minor cannot vanish modulo PRIME,
and all tested ranks and full-support kernel decisions are exact.  The field
primality, incidence-column norms, and rational rank are checked below.

The group acts by p -> c o p o r; transposition/inversion is never used.
Each representative's primitive integer kernel is independently derived by
rational elimination.  Both orientations are retained unless an actual group
element stabilizing the support sends that primitive vector to its negative.

Replay from the repository root:
  python3 evidence/census.py
Regenerate the deterministic checked data explicitly:
  python3 evidence/census.py --output /tmp/circuits.json
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
import itertools
import json
from math import gcd, isqrt, lcm
from pathlib import Path

PRIME = 65521
PERMUTATIONS = tuple(itertools.permutations(range(4)))
EXPECTED_LAYERS = (
    (1, 1, 1, 0), (2, 4, 4, 0), (3, 10, 10, 0),
    (4, 41, 40, 1), (5, 103, 101, 0), (6, 309, 292, 3),
    (7, 690, 632, 1), (8, 1446, 1178, 10),
    (9, 2391, 1568, 8), (10, 3317, 1282, 15),
    (11, 2956, 0, 35),
)


def require(condition: bool, message: str) -> None:
    """Checks deliberately remain active under python -O."""
    if not condition:
        raise ValueError(message)


def incidence() -> list[list[int]]:
    return [[int(p[i] == j) for p in PERMUTATIONS]
            for i in range(4) for j in range(4)]


def relabelings() -> tuple[tuple[int, ...], ...]:
    index = {p: k for k, p in enumerate(PERMUTATIONS)}
    group = tuple(tuple(index[tuple(c[p[r[i]]] for i in range(4))]
                        for p in PERMUTATIONS)
                  for r in PERMUTATIONS for c in PERMUTATIONS)
    require(len(set(group)) == 576, "row/column group is not faithful")
    require(all(sorted(g) == list(range(24)) for g in group),
            "a relabeling is not a permutation")
    return group


def rref(matrix: list[list[int]], prime: int | None = None
         ) -> tuple[list[list], list[int]]:
    """Independent exact rational mode and finite-field mode."""
    a = ([row[:] for row in matrix] if prime else
         [[Fraction(v) for v in row] for row in matrix])
    ncols = len(a[0]); rank = 0; pivots = []
    for col in range(ncols):
        pivot = next((r for r in range(rank, len(a)) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        if prime:
            inv = pow(a[rank][col], -1, prime)
            a[rank] = [v * inv % prime for v in a[rank]]
        else:
            factor = a[rank][col]
            a[rank] = [v / factor for v in a[rank]]
        for row in range(len(a)):
            if row == rank or not a[row][col]:
                continue
            factor = a[row][col]
            if prime:
                a[row] = [(v - factor * w) % prime
                          for v, w in zip(a[row], a[rank])]
            else:
                a[row] = [v - factor * w
                          for v, w in zip(a[row], a[rank])]
        pivots.append(col); rank += 1
        if rank == len(a):
            break
    return a, pivots


def support_of(mask: int) -> list[int]:
    return [j for j in range(24) if mask & (1 << j)]


def restricted(b: list[list[int]], support: list[int]) -> list[list[int]]:
    return [[row[j] for j in support] for row in b]


def null_vector(reduced: list[list], pivots: list[int], ncols: int,
                prime: int | None = None) -> list:
    require(len(pivots) == ncols - 1, "kernel is not one-dimensional")
    free = next(j for j in range(ncols) if j not in pivots)
    vector = [0] * ncols; vector[free] = 1
    for i, j in enumerate(pivots):
        vector[j] = (-reduced[i][free] % prime if prime else
                     -reduced[i][free])
    return vector


class Canonicalizer:
    def __init__(self, group: tuple[tuple[int, ...], ...]):
        # Each lookup gives the literal group images of one eight-bit block.
        self.lookup = []
        for block in range(3):
            table = [[0] * len(group) for _ in range(256)]
            for mask in range(1, 256):
                low = mask & -mask; bit = low.bit_length() - 1
                table[mask] = [v | (1 << g[8 * block + bit])
                               for v, g in zip(table[mask ^ low], group)]
            self.lookup.append(table)

    def __call__(self, mask: int) -> int:
        first, second, third = self.lookup
        return min(a | b | c for a, b, c in zip(
            first[mask & 255], second[(mask >> 8) & 255],
            third[(mask >> 16) & 255]))


def primitive_kernel(b: list[list[int]], support: list[int]) -> list[int]:
    reduced, pivots = rref(restricted(b, support))
    vector = null_vector(reduced, pivots, len(support))
    require(all(vector), "rational circuit kernel has a zero coordinate")
    multiplier = lcm(*(Fraction(v).denominator for v in vector))
    coefficients = [int(v * multiplier) for v in vector]
    divisor = reduce(gcd, coefficients)
    coefficients = [v // divisor for v in coefficients]
    if coefficients[0] < 0:
        coefficients = [-v for v in coefficients]
    full = [0] * 24
    for j, value in zip(support, coefficients):
        full[j] = value
    require(all(sum(v * c for v, c in zip(row, full)) == 0 for row in b),
            "primitive kernel fails a literal marginal equation")
    require(reduce(gcd, full) == 1, "kernel is not primitive")
    require(sum(full) == 0, "kernel signed mass is not zero")
    return full


def build_census() -> dict:
    require(all(PRIME % d for d in range(2, isqrt(PRIME) + 1)),
            "finite-field modulus is not prime")
    b = incidence(); group = relabelings(); canonical = Canonicalizer(group)
    require(all(sum(row[j] ** 2 for row in b) == 4 for j in range(24)),
            "incidence column norm changed")
    _, pivots = rref(b)
    require(len(pivots) == 10 and 2 ** 10 < PRIME,
            "rank or determinant bound changed")
    frontier = {0}; circuit_masks = []; layers = []
    for size in range(1, 12):
        candidates = {canonical(mask | (1 << j))
                      for mask in frontier for j in range(24)
                      if not mask & (1 << j)}
        next_frontier = set(); circuits = []
        for mask in sorted(candidates):
            support = support_of(mask)
            reduced, pivots = rref(restricted(b, support), PRIME)
            if len(pivots) == size:
                next_frontier.add(mask)
            else:
                require(len(pivots) == size - 1,
                        "extension of independent set lost more than one rank")
                vector = null_vector(reduced, pivots, size, PRIME)
                if all(vector):
                    circuits.append(mask)
        layer = (size, len(candidates), len(next_frontier), len(circuits))
        require(layer == EXPECTED_LAYERS[size - 1],
                f"census layer changed: {layer}")
        layers.append(dict(zip(("size", "candidates", "independent_orbits",
                               "circuit_orbits"), layer)))
        circuit_masks.extend(circuits); frontier = next_frontier
    require(not frontier, "rank-eleven independent sets exist")
    records = []
    for mask in sorted(circuit_masks, key=lambda m: (m.bit_count(), m)):
        support = support_of(mask); primitive = primitive_kernel(b, support)
        orbit = set(); stabilizer = 0; signs_equivalent = False
        for action in group:
            image_mask = sum(1 << action[j] for j in support)
            orbit.add(image_mask)
            if image_mask == mask:
                stabilizer += 1; image_vector = [0] * 24
                for j, value in enumerate(primitive):
                    image_vector[action[j]] = value
                if image_vector == [-v for v in primitive]:
                    signs_equivalent = True
        require(min(orbit) == mask, "support representative is not canonical")
        require(len(orbit) * stabilizer == 576, "orbit/stabilizer mismatch")
        positive_mass = sum(v for v in primitive if v > 0)
        require(positive_mass == -sum(v for v in primitive if v < 0),
                "primitive positive and negative masses differ")
        records.append(dict(
            support_mask=mask, support=support, primitive=primitive,
            positive_mass=positive_mass, support_orbit_size=len(orbit),
            stabilizer=stabilizer, signs_equivalent=signs_equivalent,
            signs=[1] if signs_equivalent else [1, -1]))
    unsigned = sum(r["support_orbit_size"] for r in records)
    oriented = sum(len(r["signs"]) for r in records)
    require((len(records), oriented, unsigned) == (73, 131, 24184),
            "final circuit totals changed")
    return dict(permutations=[list(p) for p in PERMUTATIONS], prime=PRIME,
                layers=layers, support_orbit_count=len(records),
                oriented_orbit_count=oriented, unsigned_circuit_count=unsigned,
                records=records)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="write regenerated deterministic census JSON")
    args = parser.parse_args(); result = build_census()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    else:
        expected = json.loads(Path(__file__).with_name("circuits.json").read_text())
        require(result == expected, "reconstructed census differs from circuits.json")
    print("Exact complete census: 73 support orbits, 131 oriented orbits, "
          "24184 unsigned labelled circuits; all checks passed.")


if __name__ == "__main__":
    main()
