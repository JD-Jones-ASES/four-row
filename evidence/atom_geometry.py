#!/usr/bin/env python3
"""Finite exact evidence for the supplementary atom-geometry note.

Construct permutations and trades from their mathematical descriptions,
check the duals and the two attaining families over rational polynomials,
and count the incidences of the proposed atom-simplex vertices. These are
finite checks and affine identities, not formal verification or a sampled
proof about arbitrary real laws. The note supplies the real-law argument.
Run with python3 evidence/atom_geometry.py (also supports python3 -O).
No external library or other repository file is required.
"""
from fractions import Fraction as Q
from itertools import permutations
import json

PERMS = tuple(permutations(range(4)))
IDENTITY = tuple(range(4))
INDEX = {p: i for i, p in enumerate(PERMS)}
FIXED = tuple(sum(p[i] == i for i in range(4)) for p in PERMS)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def compose(a, b):
    return tuple(a[b[i]] for i in range(4))


def inverse(p):
    return tuple(p.index(i) for i in range(4))


def swap(a, b):
    p = list(IDENTITY)
    p[a], p[b] = p[b], p[a]
    return tuple(p)


def cycle(labels):
    p = list(IDENTITY)
    for a, b in zip(labels, labels[1:] + labels[:1]):
        p[a] = b
    return tuple(p)


def vector(terms):
    result = [Q(0)] * 24
    for p, value in terms:
        result[INDEX[p]] += value
    return tuple(result)


def double_trade(a, b, c, d):
    x, y = swap(a, b), swap(c, d)
    return vector([(IDENTITY, Q(1, 2)), (compose(x, y), Q(1, 2)),
                   (x, Q(-1, 2)), (y, Q(-1, 2))])


def cycle_trade(labels):
    p = cycle(labels)
    terms = [(IDENTITY, Q(1, 2)), (p, Q(1, 4)), (inverse(p), Q(1, 4))]
    terms += [(swap(a, b), Q(-1, 4))
              for a, b in zip(labels, labels[1:] + labels[:1])]
    return vector(terms)


TRADES = (double_trade(0, 1, 2, 3), double_trade(0, 2, 1, 3),
          double_trade(0, 3, 1, 2), cycle_trade((0, 1, 2, 3)),
          cycle_trade((0, 1, 3, 2)), cycle_trade((0, 2, 1, 3)))


def rank(rows):
    matrix = [[Q(x) for x in row] for row in rows]
    pivot = 0
    for col in range(len(matrix[0])):
        found = next((i for i in range(pivot, len(matrix)) if matrix[i][col]), None)
        if found is None:
            continue
        matrix[pivot], matrix[found] = matrix[found], matrix[pivot]
        divisor = matrix[pivot][col]
        matrix[pivot] = [x / divisor for x in matrix[pivot]]
        for i in range(len(matrix)):
            if i != pivot and matrix[i][col]:
                factor = matrix[i][col]
                matrix[i] = [x - factor * y for x, y in zip(matrix[i], matrix[pivot])]
        pivot += 1
        if pivot == len(matrix):
            break
    return pivot


def tv(law):
    return sum(abs(x - Q(1, 24)) for x in law) / 2


def check_law(law, distance, mass):
    require(min(law) >= 0 and sum(law) == 1, 'Invalid probability law')
    for i in range(4):
        for j in range(4):
            require(sum(law[k] for k, p in enumerate(PERMS) if p[i] == j) == Q(1, 4),
                    'Unbalanced attaining law')
    require(tv(law) == distance, 'Incorrect total variation')
    require(law[0] == mass, 'Incorrect attaining mass')


def check_duals(dual, second):
    require(all(abs(b) <= 1 for b in dual), 'First dual exceeds the unit box')
    require(all(abs(b) <= 1 for b in second), 'Second dual exceeds the unit box')
    require(sum(dual) == 4 and sum(second) == -4, 'Incorrect dual constants')


# Each pair represents the exact affine polynomial a + b*r.
FIRST = tuple({4: (Q(1, 24), Q(1, 2)), 2: (Q(1, 24), Q(-1, 6)),
               1: (Q(1, 24), Q(0)), 0: (Q(1, 24), Q(1, 18))}[h] for h in FIXED)
MIDDLE = tuple({4: (Q(5, 48), Q(1, 4)), 2: (Q(0), Q(0)),
                1: (Q(7, 96), Q(-1, 8)), 0: (Q(5, 144), Q(1, 12))}[h] for h in FIXED)


def affine_value(pair, r):
    return pair[0] + r * pair[1]


def family(coefficients, r):
    return tuple(affine_value(pair, r) for pair in coefficients)


def check_affine_family(coefficients, lo, hi, signs, atom):
    # Coefficient comparisons certify the identities. Affine nonnegativity
    # on a closed interval is equivalent to nonnegativity at both endpoints.
    require(tuple(sum(pair[d] for pair in coefficients) for d in range(2)) == (1, 0),
            'Incorrect affine probability mass')
    for i in range(4):
        for j in range(4):
            require(tuple(sum(pair[d] for p, pair in zip(PERMS, coefficients) if p[i] == j)
                          for d in range(2)) == (Q(1, 4), 0),
                    'Incorrect affine marginal')
    for pair, sign in zip(coefficients, signs):
        require(all(affine_value(pair, r) >= 0 for r in (lo, hi)), 'Negative affine law entry')
        for r in (lo, hi):
            deviation = affine_value(pair, r) - Q(1, 24)
            require(abs(deviation) == sign * deviation, 'Incorrect affine deviation sign')
    tv_coefficients = (sum(sign * (pair[0] - Q(1, 24))
                           for pair, sign in zip(coefficients, signs)) / 2,
                       sum(sign * pair[1] for pair, sign in zip(coefficients, signs)) / 2)
    require(tv_coefficients == (0, 1), 'Incorrect affine total variation')
    require(coefficients[0] == atom, 'Incorrect affine attaining mass')
    facets = ((Q(1, 24), Q(1, 2)), (Q(5, 48), Q(1, 4)), (Q(1, 4), Q(0)))
    require(all(affine_value(atom, r) <= affine_value(facet, r) for facet in facets for r in (lo, hi)),
            'Incorrect affine envelope branch')


def check_incidence(owners):
    require(len(owners) == 108, 'Wrong number of distinct vertices')
    require(sum(len(x) == 2 for x in owners.values()) == 36, 'Wrong shared-vertex count')
    require(sum(len(x) == 1 for x in owners.values()) == 72, 'Wrong private-vertex count')
    require(sum(map(len, owners.values())) == 144, 'Wrong face/vertex incidence count')
    edges = {frozenset(x) for x in owners.values() if len(x) == 2}
    for tau in PERMS:
        neighbors = {next(iter(edge - {tau})) for edge in edges if tau in edge}
        require(len(neighbors) == 3, 'Wrong atom-face degree')
        require(all(FIXED[INDEX[compose(inverse(tau), p)]] == 0
                    and compose(compose(inverse(tau), p), compose(inverse(tau), p)) == IDENTITY
                    for p in neighbors), 'Adjacency is not a double transposition')
        require(all(frozenset((p, q)) in edges for p in neighbors for q in neighbors if p != q),
                'An adjacency component is not K4')


def reject(label, check, expected):
    try:
        check()
    except AssertionError as error:
        require(str(error) == expected, 'Negative control failed for an unintended reason: ' + label)
        return label
    raise AssertionError('Negative control was accepted: ' + label)


def main():
    # Finite dual coefficients used in the note's arbitrary-real-law argument.
    dual = tuple(4 * (p == IDENTITY) - h + 1 for p, h in zip(PERMS, FIXED))
    second = tuple(8 * (p == IDENTITY) - 2 * h + 1 + 2 * (h == 2)
                   for p, h in zip(PERMS, FIXED))
    check_duals(dual, second)

    for trade in TRADES:
        require(sum(trade) == 0 and sum(map(abs, trade)) == 2, 'Incorrect signed mass')
        require(trade[0] == Q(1, 2), 'Incorrect identity deviation')
        require(all(abs(x) == b * x for x, b in zip(trade, dual)), 'Trade off the exposed face')
        for i in range(4):
            for j in range(4):
                require(sum(trade[k] for k, p in enumerate(PERMS) if p[i] == j) == 0,
                        'Trade has nonzero marginal')
    require(rank(TRADES) == 6, 'The six rays are linearly dependent')
    allowed = [k for k, h in enumerate(FIXED) if h != 1]
    incidence = [[int(PERMS[k][i] == j) for k in allowed]
                 for i in range(4) for j in range(4)]
    require(len(allowed) == 16 and rank(incidence) == 10, 'Wrong saturation kernel dimension')

    first_signs = tuple({4: 1, 2: -1, 1: 0, 0: 1}[h] for h in FIXED)
    middle_signs = tuple(1 if h in (4, 0) else -1 for h in FIXED)
    check_affine_family(FIRST, Q(0), Q(1, 4), first_signs, (Q(1, 24), Q(1, 2)))
    check_affine_family(MIDDLE, Q(1, 4), Q(7, 12), middle_signs, (Q(5, 48), Q(1, 4)))
    require(family(FIRST, Q(1, 4)) == family(MIDDLE, Q(1, 4)), 'Families fail to join')
    # Beyond 7/12 the fixed endpoint law remains feasible and the two
    # nonconstant envelope facets increase from values at least 1/4.
    check_law(family(MIDDLE, Q(7, 12)), Q(7, 12), Q(1, 4))
    for facet in ((Q(1, 24), Q(1, 2)), (Q(5, 48), Q(1, 4))):
        require(affine_value(facet, Q(7, 12)) >= Q(1, 4) and facet[1] >= 0,
                'Incorrect constant envelope branch')

    radii = [Q(0), Q(1, 48), Q(1, 24), Q(1, 12), Q(1, 4), Q(1, 3), Q(7, 12)]
    for r in radii:
        if r <= Q(1, 4):
            law = family(FIRST, r)
            mass = Q(1, 24) + r / 2
        else:
            law = family(MIDDLE, r)
            mass = Q(5, 48) + r / 4
        check_law(law, r, mass)
        require(mass == min(Q(1, 24) + r / 2, Q(5, 48) + r / 4, Q(1, 4)),
                'Wrong branch of the atom envelope')
    for trade in TRADES:
        coefficients = tuple((Q(1, 24), x) for x in trade)
        signs = tuple((x > 0) - (x < 0) for x in trade)
        check_affine_family(coefficients, Q(0), Q(1, 12), signs, (Q(1, 24), Q(1, 2)))
        for r in [Q(0), Q(1, 24), Q(1, 12)]:
            check_law(tuple(Q(1, 24) + r * x for x in trade), r, Q(1, 24) + r / 2)

    owners = {}
    for tau in PERMS:
        for trade in TRADES:
            moved = [Q(0)] * 24
            for p, value in zip(PERMS, trade):
                moved[INDEX[compose(tau, p)]] = value
            owners.setdefault(tuple(moved), set()).add(tau)
    check_incidence(owners)

    # Corrupt one feature at a time and require the intended check to reject it.
    wrong_dual = (-dual[0],) + dual[1:]
    unbalanced = [Q(1, 24)] * 24
    unbalanced[0] += Q(1, 48)
    unbalanced[INDEX[swap(0, 1)]] -= Q(1, 48)
    negative = tuple(Q(1, 24) + Q(1, 6) * x for x in TRADES[0])
    missing_vertex = dict(owners)
    missing_vertex.pop(next(iter(missing_vertex)))
    wrong_affine = list(FIRST)
    wrong_affine[0] = (Q(1, 24), Q(1, 3))
    controls = [
        reject('wrong dual sign', lambda: check_duals(wrong_dual, second), 'Incorrect dual constants'),
        reject('unbalanced law', lambda: check_law(unbalanced, Q(1, 48), Q(1, 16)),
               'Unbalanced attaining law'),
        reject('negative balanced law', lambda: check_law(negative, Q(1, 6), Q(1, 8)),
               'Invalid probability law'),
        reject('wrong radius', lambda: check_law(family(FIRST, 0), Q(1, 48), Q(1, 24)),
               'Incorrect total variation'),
        reject('deleted incidence vertex', lambda: check_incidence(missing_vertex),
               'Wrong number of distinct vertices'),
        reject('wrong affine slope', lambda: check_affine_family(
            wrong_affine, Q(0), Q(1, 4), first_signs, (Q(1, 24), Q(1, 2))),
               'Incorrect affine probability mass'),
    ]
    print(json.dumps({'status': 'passed', 'arithmetic': 'exact fractions',
                      'dual_coordinates': 48, 'independent_rays': 6,
                      'saturation_kernel_rank': 10, 'rational_family_controls': len(radii),
                      'affine_family_identities': 8, 'negative_controls': controls,
                      'atom_faces': 24, 'distinct_vertices': 108,
                      'shared_vertices': 36, 'private_vertices': 72,
                      'adjacency_components': 'six K4',
                      'scope': 'finite exact evidence and affine identities for a supplementary note; '
                               'not formal verification or a sampled proof for arbitrary real laws'}, indent=2))


if __name__ == '__main__':
    main()
