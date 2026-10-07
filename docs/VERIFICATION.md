# Verification and reproduction

The release gate is a successful **full** private Linux verification run on
the exact commit. Its recorded commit, clean worktree, axiom audit, statement
comparison, and independent-kernel verdicts are the verification record.
A partial certificate build or sandbox smoke is not the completed gate.

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
python3 scripts/fetch_mathlib_cache.py
python3 scripts/build_grams.py --jobs 1
python3 scripts/build_census.py
lake build
python3 scripts/audit_release.py
python3 evidence/probe.py
python3 evidence/audit_census.py
git diff --check
```

The sequential prebuild commands are the conservative local route. A direct
cold `lake build FourRowSolution` also follows explicit private import chains:
two Gram chains (G000–G064 and G065–G130), plus one census chain through table
checks, maximal-support witnesses, independence, and support extensions.
Thus at most three large certificate modules compile simultaneously; other
modules may also compile, so this is not a total process or memory bound.
The ordering imports add no mathematical assumption and leave theorem bodies
unchanged. `--jobs 1` remains the conservative Gram-builder default.
`FOUR_ROW_LAKE` selects the Lake executable
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
two Gram jobs and one census job check the certificate chains against the
same immutable source. Checked artifacts, including private proof data and
census phase parents, are transferred to the dependent verification job,
which builds the exhaustive census and the full public API, audits all
principal axioms, and runs the two exact Python replays.

The final step runs the toolchain's `lake comparator` with the named
Challenge and Solution. A temporary config enables the bundled NanoDa and
con-ron independent kernels. For the private runner's memory budget, a
temporary launcher runs NanoDa with one worker and treats unpermitted
axioms as hard errors; it preserves the exported declarations and axiom
allowlist. Con-ron runs in verified mode with one worker. The committed
comparator config stays within
Palomar's accepted authoring schema. The checker runs use bubblewrap from
the pinned official installer. The complete verification job adds 16 GiB of
swap as memory headroom for the full exported proof closure. The private
workflow does not contact the
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

## Direct cold-build diagnostic

[The cold-build workflow](../.github/workflows/cold-build.yml) starts with no
project build artifacts, retrieves only the pinned Mathlib cache, and runs
`lake build FourRowSolution` with `LEAN_NUM_THREADS=16`. It records process,
resident-memory, swap, pressure, and elapsed-time samples. This checks the
direct build route used by the inspected submission tooling, on the smaller
private GitHub runner; it is not an official submission preflight.

[The diagnostic record](../verification/cold-build.json) preserves the earlier
unbounded-layout run. It was cancelled after one hour: sixteen concurrent
Lean compilers caused sustained swap thrashing, with no Lean error or OOM
kill recorded. That observation motivated the import chains. Cancellation
does not establish a failed theorem or a failure on official hardware.

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
The generator clears rational denominators using a positive integer scale.
Every emitted identity is checked by kernel reduction of sparse integer
polynomials. The shared checker proves that expansion, structural sorting,
and coefficient collection preserve evaluation for every real assignment;
it also proves nonnegativity from the checked integer square weights.
A definitional evaluation bridge and a checked scalar identity recover
each original real quartic statement by dividing by the positive scale,
including the positive defect used in the full equality classification.
Python generation is therefore certificate construction,
not an additional trusted computation.

## Publication boundary

The repository remains private. JD controls any later visibility change
and Palomar submission. The exact compared statements define the formal
scope; historical research notes may discuss further unformalized
consequences. Neither verification nor registration establishes worldwide
novelty or external mathematical peer review.
