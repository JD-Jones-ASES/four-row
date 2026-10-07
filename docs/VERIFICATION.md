# Verification and reproduction

## Checked proof

The [complete Linux verification](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572525271)
passed the full Lean build, all sixteen statement comparisons and axiom
audits, exact evidence replays, and independent checking by con-ron,
NanoDa, and Lean. The [direct cold build](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572527284)
also passed.

The kernel-checked source is `c207efc787a7e1c88aae29dc92d4be5e10297bf2`.
[proof.json](../verification/proof.json) identifies its checks and the exact
proof/build inputs present in this package. Python executable hashes exclude
docstrings. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The Mathlib-only Challenge has intentional theorem placeholders;
the Solution does not import them.

## Local reproduction

Use elan, Python 3, and the committed toolchain and dependency pins:

```sh
python3 scripts/fetch_mathlib_cache.py
python3 scripts/build_grams.py --jobs 1
python3 scripts/build_census.py
lake build
python3 scripts/audit_release.py
python3 evidence/probe.py
python3 evidence/audit_census.py
```

`audit_release.py` checks source-module resolution, the Challenge import
boundary, proof-hole exclusions, dependency pins, and each theorem's axioms.

The sequential prebuilds limit memory use. Direct `lake build FourRowSolution`
uses two Gram import chains and one census chain; other modules can compile
concurrently. `FOUR_ROW_LAKE` selects the Lake executable for the Gram builder
and release audit; the census builder accepts `--lake`.

## Independent kernel replay

Run the [Linux verification workflow](../.github/workflows/verify.yml):

```sh
gh workflow run verify.yml --ref main -f stage=full
```

The `full` stage builds the certificate chains and public API, audits axioms,
replays the exact evidence, and invokes the bundled `lake comparator` in
bubblewrap. con-ron runs in verified mode with one worker; NanoDa runs with
one worker and rejects unpermitted axioms. The workflow records the checked
commit and worktree status. The `certificates` and `census` stages check
only their named components. The [cold-build workflow](../.github/workflows/cold-build.yml)
checks a direct Solution build without project artifacts.

## Exact evidence

[SOURCE.json](../evidence/SOURCE.json) records hashes of the packaged evidence.
The main replay checks circuit coverage, rational polynomial identities,
positive pivots, equality blocks, stability identities, and corruption controls.
The census audit independently implements rational elimination and orbit
traversal. Python produces witnesses; Lean proves their checks and soundness.

The supplementary [atom-geometry note](ATOM_GEOMETRY.md) has a separate
finite rational checker:

```sh
python3 evidence/atom_geometry.py
python3 -O evidence/atom_geometry.py
```

This checks affine identities, trades, incidence counts, and corruption
controls. The note's general statements rely on its written proofs and are
outside the [compared Lean declarations](THEOREMS.md).
