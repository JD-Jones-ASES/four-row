"""Independent rational audit of the complete four-row circuit census.

This optional replay uses no source imports from the primary census and no
modular arithmetic, numerical libraries, or determinant-size assumption.
Integer cross-multiplication gives exact rational echelon forms; Fraction
back-substitution checks one-dimensional kernel supports.  Symmetry reduction
removes literal complete orbits from each candidate pool, independently of
the primary implementation's eight-bit lookup canonicalizer.

The shared mathematical enumeration principle is to extend every independent
support orbit.  Deleting any element of a circuit leaves an independent set,
so all circuits occur by rank plus one.  This audit was written by the
independent mathematical review agent after reviewing the primary census;
it does not claim an independent discovery of that enumeration principle.

Run from the repository root:
  python3 evidence/audit_census.py
"""

from fractions import Fraction
from functools import reduce
from itertools import permutations
import json
from math import gcd
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def echelon(matrix):
    """Exact rational elimination, implemented using integer row operations."""
    work = [row[:] for row in matrix]
    pivots = []
    for column in range(len(work[0])):
        height = len(pivots)
        selected = next((i for i in range(height, len(work))
                         if work[i][column]), None)
        if selected is None:
            continue
        work[height], work[selected] = work[selected], work[height]
        pivot = work[height][column]
        for i in range(height + 1, len(work)):
            entry = work[i][column]
            if entry:
                new = [pivot * a - entry * b
                       for a, b in zip(work[i], work[height])]
                divisor = reduce(gcd, new)
                work[i] = [a // divisor for a in new] if divisor else new
        pivots.append(column)
        if len(pivots) == len(work):
            break
    return work, pivots


def classify(matrix):
    """Return rational rank and whether the columns form a circuit."""
    work, pivots = echelon(matrix)
    columns = len(work[0])
    if len(pivots) != columns - 1:
        return len(pivots), False
    free = next(i for i in range(columns) if i not in pivots)
    kernel = [Fraction(int(i == free)) for i in range(columns)]
    for row, column in reversed(list(enumerate(pivots))):
        kernel[column] = -sum((work[row][j] * kernel[j]
                               for j in range(column + 1, columns)),
                              Fraction()) / work[row][column]
    require(all(sum(a * b for a, b in zip(row, kernel)) == 0
                for row in matrix), "rational back-substitution failed")
    return len(pivots), all(kernel)


def audit(path):
    saved = json.loads(path.read_text())
    perms = list(permutations(range(4)))
    index = {p: i for i, p in enumerate(perms)}
    require(saved["permutations"] == [list(p) for p in perms],
            "permutation order differs")
    incidence = [[int(p[i] == j) for p in perms]
                 for i in range(4) for j in range(4)]
    _, pivots = echelon(incidence)
    rank = len(pivots)
    require(rank == 10, "incidence rank differs")
    # Opposite row-action convention from the primary implementation.
    actions = []
    for row in perms:
        inverse = [row.index(i) for i in range(4)]
        for column in perms:
            actions.append(tuple(index[tuple(column[p[inverse[i]]]
                                              for i in range(4))] for p in perms))
    require(len(set(actions)) == 576, "row/column actions are not distinct")
    require(all(sorted(g) == list(range(24)) for g in actions),
            "invalid row/column action")

    def support(mask):
        return [i for i in range(24) if mask & (1 << i)]

    def orbit(mask):
        selected = support(mask)
        return {sum(1 << action[i] for i in selected) for action in actions}

    frontier = {0}
    circuits = set()
    for size in range(1, rank + 2):
        pending = {mask | (1 << i) for mask in frontier
                   for i in range(24) if not mask & (1 << i)}
        representatives = set()
        while pending:
            images = orbit(pending.pop())
            pending.difference_update(images)
            representatives.add(min(images))
        next_frontier = set()
        new_circuits = set()
        for mask in representatives:
            selected = support(mask)
            require(len(selected) == size, "candidate size differs")
            restricted = [[row[i] for i in selected] for row in incidence]
            subrank, circuit = classify(restricted)
            require(subrank in (size, size - 1),
                    "extension of an independent set lost extra rank")
            if subrank == size:
                next_frontier.add(mask)
            elif circuit:
                new_circuits.add(mask)
        expected = saved["layers"][size - 1]
        observed = {"size": size, "candidates": len(representatives),
                    "independent_orbits": len(next_frontier),
                    "circuit_orbits": len(new_circuits)}
        require(observed == expected, f"census layer mismatch: {observed}")
        print("Rational audit:", observed, flush=True)
        circuits.update(new_circuits)
        frontier = next_frontier
    require(not frontier, "unexamined independent frontier remains")
    require(len(saved["layers"]) == rank + 1, "unexpected saved census layers")
    records = saved["records"]
    require(len(records) == len(circuits), "duplicate or missing circuit records")
    require({r["support_mask"] for r in records} == circuits,
            "complete circuit support set differs")

    unsigned_count = 0
    oriented_count = 0
    for record in records:
        mask = record["support_mask"]
        selected = support(mask)
        primitive = record["primitive"]
        require(len(primitive) == 24 and all(type(v) is int for v in primitive),
                "invalid primitive kernel vector")
        require([i for i, v in enumerate(primitive) if v] == selected == record["support"],
                "primitive kernel support differs")
        require(reduce(gcd, primitive) == 1 and primitive[selected[0]] > 0,
                "primitive normalization differs")
        require(all(sum(a * b for a, b in zip(row, primitive)) == 0
                    for row in incidence), "primitive vector is outside kernel")
        positive = sum(v for v in primitive if v > 0)
        require(sum(primitive) == 0 and positive == record["positive_mass"],
                "positive mass differs")
        images = orbit(mask)
        stabilizer = 0
        flips_sign = False
        for action in actions:
            image = [0] * 24
            for i, value in enumerate(primitive):
                image[action[i]] = value
            if [i for i, v in enumerate(image) if v] == selected:
                stabilizer += 1
                flips_sign |= image == [-v for v in primitive]
        require(min(images) == mask, "noncanonical support representative")
        require(len(images) == record["support_orbit_size"] and
                stabilizer == record["stabilizer"] and len(images) * stabilizer == 576,
                "orbit/stabilizer mismatch")
        require(flips_sign == record["signs_equivalent"] and
                record["signs"] == ([1] if flips_sign else [1, -1]),
                "orientation coverage differs")
        unsigned_count += len(images)
        oriented_count += len(record["signs"])
    require(len(records) == saved["support_orbit_count"] == 73,
            "support orbit count differs")
    require(oriented_count == saved["oriented_orbit_count"] == 131,
            "oriented orbit count differs")
    require(unsigned_count == saved["unsigned_circuit_count"] == 24184,
            "unsigned labelled circuit count differs")
    print("Independent rational census audit passed: 73 support orbits, "
          "131 oriented orbits, 24184 unsigned labelled circuits.", flush=True)


if __name__ == "__main__":
    audit(Path(__file__).with_name("circuits.json"))
