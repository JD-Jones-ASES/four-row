"""Exact four-site column input for the strict permanent inequality.

This is an independent finite-group calculation, using only the standard
library.  It is not a proof of a global shuffle moment or mixing theorem.

Published mathematical convention inspected at OpenAI/math commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, in
preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/
build/sections/03-recursion.tex, lines 4--14, 23--27, 42--46, 91--92,
and 150--161.  Products gh apply h first.  A two-axis sweep is M=VH,
where H and V average the independent fair switches on opposite square
edges.  Since each layer is a self-adjoint projection, M* M=HVH.
The source's column law is (M* M)^k, with k equal to half its even moment.
No source implementation was consulted or imported.

All-powers proof.  Let D be the order-eight subgroup preserving the
unordered partition {{0,1},{2,3}}, and write d,u for the uniform laws on D
and S4.  The literal group calculation below proves mu=(d+3u)/4, d*d=d,
d*u=u*d=u, and u*u=u.  Hence, by induction for every integer k>=1,

    mu^k = 4^(-k) d + (1-4^(-k)) u.

The eight points in D have positive excess 4^(-k)*(1/8-1/24), and the
sixteen other points have negative excess -4^(-k)/24.  Consequently
TV(mu^k,u)=(2/3)*4^(-k).  D is transitive, so every displayed mixture has
uniform coordinate marginals.  This is an algebraic induction, not an
inference from the finite checks for k=1,2,3.

Thus k=3 has radius 1/96, p=95/48, and theta=1-1/p=47/95 under the
explicit strict permanent bound p(rho)=2-(1-24*rho)/36.  This makes the
permanent-input condition valid for even moments >=6.  The source's other
sparse and finite-size requirements can require a larger moment.  Its
tree-parameter choice delta=(1/2-theta)/2 gives b=188/189 and eta=1/378;
these are substitutions into that argument, not a new global theorem.

Replay: python3 evidence/shuffle_input.py
All checks remain active under python -O.
"""

from fractions import Fraction as Q
from itertools import permutations
import json


PERMUTATIONS = tuple(permutations(range(4)))
IDENTITY = tuple(range(4))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def compose(g, h):
    """g h applies h first, as in the inspected source."""
    return tuple(g[h[i]] for i in range(4))


def inverse(g):
    return tuple(g.index(i) for i in range(4))


def uniform(group):
    return {g: Q(int(g in group), len(group)) for g in PERMUTATIONS}


def convolution(a, b):
    result = {g: Q(0) for g in PERMUTATIONS}
    for g in PERMUTATIONS:
        for h in PERMUTATIONS:
            result[compose(g, h)] += a[g] * b[h]
    return result


def mixture(a, b, weight):
    return {g: weight * a[g] + (1 - weight) * b[g]
            for g in PERMUTATIONS}


def check_subgroup(group, size):
    require(len(group) == size and IDENTITY in group, "subgroup size/identity")
    require(all(inverse(g) in group for g in group), "subgroup inverse")
    require(all(compose(g, h) in group for g in group for h in group),
            "subgroup closure")


def check_balanced(law):
    require(set(law) == set(PERMUTATIONS), "wrong law support keys")
    require(all(v >= 0 for v in law.values()) and sum(law.values()) == 1,
            "invalid probability law")
    require(all(sum(law[g] for g in PERMUTATIONS if g[i] == j) == Q(1, 4)
                for i in range(4) for j in range(4)),
            "incorrect coordinate marginal")


def require_same(a, b):
    require(a == b, "incorrect convolution identity")


def rejected(function, expected):
    try:
        function()
    except ValueError as error:
        require(expected in str(error), "wrong negative-control rejection")
    else:
        raise ValueError("negative control was accepted")


def run_checks():
    horizontal = {g for g in PERMUTATIONS if {g[0], g[1]} == {0, 1}}
    vertical = {g for g in PERMUTATIONS if {g[0], g[2]} == {0, 2}}
    blocks = {frozenset({0, 1}), frozenset({2, 3})}
    dihedral = {g for g in PERMUTATIONS
                if {frozenset({g[0], g[1]}), frozenset({g[2], g[3]})} == blocks}
    for group, size in [(horizontal, 4), (vertical, 4), (dihedral, 8)]:
        check_subgroup(group, size)
    h, v, d, u = map(uniform, [horizontal, vertical, dihedral, PERMUTATIONS])
    require_same(convolution(h, h), h)
    require_same(convolution(v, v), v)
    sweep = convolution(v, h)
    adjoint = {g: sweep[inverse(g)] for g in PERMUTATIONS}
    mu = convolution(adjoint, sweep)
    require_same(mu, convolution(convolution(h, v), h))
    require_same(mu, mixture(d, u, Q(1, 4)))
    require_same(convolution(mu, mu), mixture(mu, u, Q(1, 4)))
    for a, b, target in [(d, d, d), (d, u, u), (u, d, u), (u, u, u)]:
        require_same(convolution(a, b), target)
    check_balanced(d)
    check_balanced(u)

    powers = []
    law = uniform({IDENTITY})
    for k, expected_tv in [(1, Q(1, 6)), (2, Q(1, 24)), (3, Q(1, 96))]:
        law = convolution(law, mu)
        require_same(law, mixture(d, u, Q(1, 4**k)))
        check_balanced(law)
        tv = sum(abs(law[g] - u[g]) for g in PERMUTATIONS) / 2
        require(tv == expected_tv == Q(2, 3 * 4**k), "incorrect TV distance")
        powers.append({"k": k, "tv": str(tv)})

    p = 2 - (1 - 24 * Q(1, 96)) / 36
    theta = 1 - 1 / p
    margin = Q(1, 2) - theta
    delta = margin / 2
    b = theta / (Q(1, 2) - delta)
    eta = (1 - b) / 2
    require((p, theta, margin, delta, b, eta) ==
            (Q(95, 48), Q(47, 95), Q(1, 190), Q(1, 380),
             Q(188, 189), Q(1, 378)), "incorrect exponent substitution")
    rejected(lambda: require_same(mu, mixture(d, u, Q(1, 3))),
             "incorrect convolution identity")
    rejected(lambda: require_same(mu, convolution(h, h)),
             "incorrect convolution identity")
    rejected(lambda: check_balanced(uniform({IDENTITY})),
             "incorrect coordinate marginal")
    return {
        "scope": "exact four-site column law; no global mixing claim",
        "subgroup_orders": [4, 4, 8],
        "all_powers_identity": "mu^k = 4^(-k) d + (1-4^(-k)) u, k >= 1",
        "all_powers_tv": "(2/3)*4^(-k), k >= 1",
        "powers": powers,
        "k3_exponents": {"p": str(p), "theta": str(theta),
                         "half_minus_theta": str(margin), "eta": str(eta)},
        "negative_controls": 3,
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), sort_keys=True))
