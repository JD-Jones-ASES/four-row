# Verification and reproduction

## Completed proof verification

The complete [Linux run](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572525271)
passed at the clean proof commit
`c207efc787a7e1c88aae29dc92d4be5e10297bf2` on October 7, 2026.
It checked the full Lean build, all sixteen principal statement comparisons
and their transitive definition closure, all sixteen axiom audits, and both
exact Python evidence replays. The only axioms were `propext`,
`Classical.choice`, and `Quot.sound`.

| Replay | Result |
|---|---|
| con-ron, verified mode, one worker | Accepted 36,724 declarations; 35,929 checks completed |
| NanoDa, one worker | Accepted; unpermitted axioms treated as hard errors |
| Lean default kernel | Accepted |
| Original bundled Comparator | Exit 0; “Your solution is okay!” |

The complete Comparator step took 2 hours 42 minutes 3 seconds. Its outer
process RSS is not an aggregate memory measurement of the checkers.

The [direct cold Solution build](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572527284)
also passed at that clean commit: 3,547 build jobs, including 285 project
modules, in 5,931.62 seconds. It began without project build artifacts and
used only the pinned Mathlib cache, with `LEAN_NUM_THREADS=16`. The runner
had two CPUs, about 7.75 GiB RAM, and 19 GiB swap. No OOM event was observed.
This is a successful build on that runner, not equivalence to Palomar's
official hardware profile.

The [archived logs and audits](https://github.com/JD-Jones-ASES/four-row/blob/1bba389f3264084890bafdffe499494f42d1655a/verification/runs/c207efc787a7e1c88aae29dc92d4be5e10297bf2/README.md)
are pinned by `evidence/2026-10-07-c207efc`; the source tag is
`verified/2026-10-07-c207efc`. Earlier census-only measurements and the
cancelled unbounded cold-build diagnostic remain in
[census.json](../verification/census.json) and
[cold-build.json](../verification/cold-build.json). They are historical
diagnostics, not substitutes for the complete successful run.

## Documentation revision

The current revision updates prose, metadata, the packaged-evidence manifest,
and Python documentation strings. Every Lean file, dependency pin, Comparator
configuration, and workflow is byte-identical to the verified proof commit.
Python executable syntax is unchanged after removing documentation strings.
[documentation-refresh.json](../verification/documentation-refresh.json)
records the comparison, current-policy validation, and documentation checks.

This is evidence that the previously verified proof inputs are preserved;
it is not a new full Linux kernel replay at the documentation commit. A future
change to mathematical code, definitions, dependencies, or executable build
logic needs fresh verification appropriate to that change. Palomar verifies
the exact commit supplied at submission independently.

## Pinned inputs

| Input | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `a98628e16c11f5167f16124105ddce53efa9bfe5` |
| PalomarPolicy, checked October 7 | `96b034cc31a72a63d4f4041911dce337a85c9a04` |
| PalomarSubmission, checked October 7 | `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |

[lake-manifest.json](../lake-manifest.json) pins the transitive dependencies.
The policy and tooling pins identify the inspected requirements, not registry
acceptance. [Submission details](PALOMAR.md) summarize the current contract.

## Local build

With elan and Python 3 installed, run from the repository root:

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
`lake build FourRowSolution` follows two Gram chains, G000–G064 and
G065–G130, and one census chain. At most three large certificate modules
compile simultaneously; other modules may also compile, so this is not a
total process or memory bound. Private ordering imports add no mathematical
assumption. `FOUR_ROW_LAKE` selects the Lake executable for the Gram builder
and release audit; the census builder accepts `--lake`.

`audit_release.py` checks unique Challenge/Solution module resolution, the
Mathlib-only Challenge boundary, proof-hole exclusions, immutable dependency
pins, and `#print axioms` for all sixteen principal theorems.
`FourRowChallenge.lean` intentionally has sixteen theorem placeholders;
the Solution never imports them.

## Linux workflow

[verify.yml](../.github/workflows/verify.yml) is manually dispatched:

```sh
gh workflow run verify.yml --ref main -f stage=full
```

Two Gram jobs and one census job check the certificate chains at the same
commit. The verification job checks the transferred proof artifacts, completes
the census and public API, audits the axioms, runs the exact evidence replays,
and invokes the original bundled `lake comparator` in bubblewrap.

A temporary configuration uses the bundled con-ron and NanoDa checkers with
one worker each. NanoDa rejects unpermitted axioms as hard errors; con-ron
uses verified mode. These resource settings preserve the exported declarations
and axiom allowlist. The job provisions swap for the smaller hosted runner.
The committed Comparator configuration stays within Palomar's authoring schema.

Only a completed `full` run counts as complete independent replay. The
`certificates` stage is a development diagnostic. The workflow records the
exact commit, worktree status, and verification logs. The separate
[cold-build workflow](../.github/workflows/cold-build.yml) measures the direct
Solution build without project artifacts.

## Evidence and generation

[SOURCE.json](../evidence/SOURCE.json) records the packaged evidence hashes
and their relation to the verified proof snapshot. `evidence/probe.py`
regenerates the circuit census and checks rational identities, positive pivots,
equality blocks, the scalar stability identity, and thirteen corruption
controls. `evidence/audit_census.py` independently implements rational
elimination and orbit traversal.

The generators emit literal data and Lean propositions. Lean's kernel checks
the support witnesses and sparse integer polynomial identities. A proved
normalizer preserves polynomial evaluation, and exact positive denominator
clearing transfers the certificates to the real inequalities. Python is a
certificate producer, not part of the theorem's axiom assumptions.

The compared declarations define the formal scope. Supplementary application
notes include further informal consequences. Mechanical verification does
not establish worldwide novelty or external mathematical peer review.
