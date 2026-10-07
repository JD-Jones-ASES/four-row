"""Replay the complete exact proof of R_4(2)=1/24; no numerical solver needed."""

from copy import deepcopy
from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path
import sys


from verify import (
    check_bundle, check_certificate, check_law, positive_pivots, require,
)
from extensions import run_checks as extension_checks
from shuffle_input import run_checks as shuffle_checks


HERE = Path(__file__).resolve().parent


def rejected(function, message):
    try:
        function()
    except ValueError as error:
        require(message in str(error), f"wrong negative-control failure: {error}")
    else:
        raise ValueError(f"negative control was accepted: {message}")


def sharpness_controls():
    perms = list(permutations(range(4)))
    trade = []
    for p in perms:
        fixed = sum(p[i] == i for i in range(4))
        trade.append(Q(1, 2) if fixed == 4 else Q(1, 18) if fixed == 0
                     else -Q(1, 6) if fixed == 2 else Q(0))
    require(sum(trade) == 0 and sum(map(abs, trade)) == 2,
            "sharpness trade mass mismatch")
    for i in range(4):
        for j in range(4):
            require(sum(v for v, p in zip(trade, perms) if p[i] == j) == 0,
                    "sharpness trade changes a marginal")
    for delta in [Q(1, 24), Q(1, 20), Q(1, 4)]:
        law = [Q(1, 24) + delta * v for v in trade]
        require(all(v >= 0 for v in law), "sharpness law has negative mass")
        require(sum(abs(v - Q(1, 24)) for v in law) / 2 == delta,
                "sharpness TV mismatch")
        ratio = 16 * law[0]
        require(ratio == Q(2, 3) + 8 * delta, "sharpness ratio mismatch")
        require(ratio == 1 if delta == Q(1, 24) else ratio > 1,
                "sharpness endpoint/violation control failed")
    rejected(lambda: check_law([1 + 24 * Q(1, 20) * v for v in trade]),
             "TV radius exceeded")


def negative_controls(bundle, records):
    cert = bundle["certificates"][0]
    damaged = deepcopy(cert)
    damaged["K"][0][0][0] = str(Q(damaged["K"][0][0][0]) + 1)
    rejected(lambda: check_certificate(damaged), "quartic coefficient identity")
    damaged = deepcopy(cert)
    damaged["E"] = damaged["E"][:-1]
    rejected(lambda: check_certificate(damaged), "mismatched block arrays")
    damaged = deepcopy(cert)
    damaged["blocks"][0][0][0] = 16
    rejected(lambda: check_certificate(damaged), "invalid quadratic monomial")
    missing = dict(bundle, certificates=bundle["certificates"][:-1])
    rejected(lambda: check_bundle(missing, records), "certificate coverage mismatch")
    rejected(lambda: positive_pivots([[Q(1), Q(2)], [Q(2), Q(1)]]),
             "nonpositive Gram pivot")
    wrong = list(map(Q, cert["weights"]))
    wrong[0] += 1
    rejected(lambda: check_certificate(cert, wrong), "does not match circuit")
    unbalanced = [Q(1)] * 24
    unbalanced[0] += Q(1, 100)
    unbalanced[1] -= Q(1, 100)
    rejected(lambda: check_law(unbalanced), "incorrect marginal")
    sharpness_controls()


def main():
    from census import build_census
    census = build_census()
    saved = json.loads((HERE / "circuits.json").read_text())
    require(census == saved, "fresh circuit census differs from saved artifact")
    bundle = json.loads((HERE / "certificates.json").read_text())
    results = check_bundle(bundle, census["records"])
    negative_controls(bundle, census["records"])
    extensions = extension_checks()
    shuffle = shuffle_checks()
    print(json.dumps({"scope": "complete exact finite proof of R_4(2)=1/24",
                      "support_orbits": len(census["records"]),
                      **results, "negative_controls": 8,
                      "extensions": extensions, "shuffle_input": shuffle}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
