# Verification and reproduction

Release verification is in progress. This file describes the reproducible
checks; a successful partial build is not the completed release gate.

## Pinned inputs

| Input | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `a98628e16c11f5167f16124105ddce53efa9bfe5` |
| Source research and extensions | Analytic-Lab `a763c72511bef8bb915449576581222a9dc1fb05` |
| Original endpoint proof | Analytic-Lab `c054cfc1669b4c5d1b58438a1bc9742e52fcd63d` |
| Policy inspected for this package | PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04` |
| Official verification tooling inspected | PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |

All transitive dependencies are pinned by [lake-manifest.json](../lake-manifest.json).
The policy and tooling pins document the verification target, not registry
acceptance. Policy can change before a later submission.

## Local build

With elan and Python 3 installed, from the repository root:

```sh
lake exe cache get
python3 scripts/build_grams.py --jobs 1
python3 scripts/build_census.py
lake build
python3 scripts/audit_release.py
python3 evidence/probe.py
python3 evidence/audit_census.py
git diff --check
```

Prebuilding the generated certificates sequentially bounds memory use. A
plain `lake build` from a cold cache can launch too many large independent
proofs simultaneously. `--jobs 1` is the conservative default; use more
only with sufficient memory. `FOUR_ROW_LAKE` selects the Lake executable
for the Gram builder and release audit; the census builder has `--lake`.

`audit_release.py` checks that the Challenge and Solution resolve uniquely
to this repository in Lake's actual source search path. It checks the
Mathlib-only contract boundary, source proof-hole exclusions, immutable
dependency pins, and `#print axioms` for every compared principal theorem.
Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. No custom
census axiom or native-decision axiom is permitted in the solution.

`FourRowChallenge.lean` intentionally has sixteen theorem holes. It is the
independent statement of record, and its holes are never imported into
`FourRowSolution.lean` or the mathematical proof modules.

## Private Linux verification

[The workflow](../.github/workflows/verify.yml) is manually dispatched. Its
eight Gram jobs and eight census jobs check disjoint certificate sets against
the same immutable source. Checked artifacts are transferred to the dependent verification
job, which builds the exhaustive census and the full public API, audits all
principal axioms, and runs the two exact Python replays.

The final step runs the toolchain's `lake comparator` with the named
Challenge and Solution. A temporary config enables the bundled NanoDa and
con-ron independent kernels. The committed comparator config stays within
Palomar's accepted authoring schema. The checker runs use bubblewrap from
the pinned official installer. The private workflow does not contact the
submission service or create a registry entry.

```sh
gh workflow run verify.yml --ref main -f stage=full
```

The `certificates` stage is a development diagnostic. Only a completed
`full` run, including statement comparison and both independent kernels,
counts as a verified release. The workflow records its exact source SHA,
worktree status, build logs, comparison output, and axiom audit in private
Actions artifacts. A cached proof never substitutes for the independent
replay of the exported declarations.

## Research evidence and generation

[SOURCE.json](../evidence/SOURCE.json) records hashes of the original Lab
files before the standalone import-path adjustment to `probe.py`.
`evidence/probe.py` independently regenerates the source census and checks
the original exact polynomial identities, positive pivots, equality blocks,
scalar stability identity, finite shuffle calculation, and thirteen
corruption controls. `evidence/audit_census.py` uses an independently
implemented rational elimination and orbit traversal.

The formal census adds exact integer left-inverse and support-extension
witnesses in `evidence/support-closure.json`. The generators in `scripts/`
emit literal data and Lean propositions. These are checked by Lean's
kernel; Python is not part of the theorem's trust assumptions.

The formal Gram generator strengthens the source certificates by retaining
an explicit positive sum of squares of row/column product differences.
Every emitted identity is checked by `ring`, and its nonnegativity is proved
in Lean. The positive defect supplies the full equality classification.

## Publication boundary

The repository remains private. JD controls any later visibility change
and Palomar submission. The exact compared statements define the formal
scope; historical research notes may discuss further unformalized
consequences. Neither verification nor registration establishes worldwide
novelty or external mathematical peer review.
