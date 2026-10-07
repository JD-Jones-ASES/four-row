# four-row

A private formalization of sharp robustness and stability for the four-row
permanent inequality, based on Analytic-Lab's October 6, 2026 handoff.

The mathematical research is recorded in [the endpoint note](docs/ENDPOINT.md)
and [the extensions](docs/EXTENSIONS.md). The
[sixteen principal statements](docs/THEOREMS.md) include full real-law
coverage, boundary cases, sharpness, entropy and adaptive histories. Complete
Lean assembly, exact statement comparison, and independent kernel replay form
the [release verification gate](docs/VERIFICATION.md).
No publication or Palomar submission has been made.

For every balanced real probability law on the 24 permutations within total
variation distance `0 ≤ r ≤ 1/24` of uniform, and nonnegative rows normalized in
probability L², the principal stability theorem is

```text
1 − Eν ∏ᵢ fᵢ(σ(i)) ≥ ((1 − 24r)/9) ∑ᵢ Var(fᵢ).
```

The coefficient is optimal at each radius, and the exact radius at exponent
two is `1/24`. Boundary matrices and arbitrary real laws are part of the
statement. Worldwide novelty and external mathematical peer review are not
asserted.

## Reproduce the evidence

```sh
python3 evidence/probe.py
python3 evidence/audit_census.py
```

The standard-library replay regenerates the full 73-support/131-orientation
census, verifies the rational Gram identities and positive pivots, and runs
thirteen corruption controls. It does not replace the Lean proof.

## Build the formalization

Install the pinned Lean toolchain with elan, then run:

```sh
python3 scripts/fetch_mathlib_cache.py
python3 scripts/build_grams.py --jobs 1
python3 scripts/build_census.py
lake build
python3 scripts/audit_release.py
```

`lean-toolchain` and `lake-manifest.json` pin Lean and all dependencies.
The generated Gram modules contain explicit sum-of-squares proofs with
exact denominator clearing. Python generates source text; Lean checks the
integer polynomial identities and their return to the real inequalities.
The generation script and original certificate data are committed.
See [verification and reproduction](docs/VERIFICATION.md) for the source
guards, private Linux workflow, statement comparison and independent kernels.

## Provenance

The research source is Analytic-Lab commit
`a763c72511bef8bb915449576581222a9dc1fb05`; the original endpoint snapshot is
`c054cfc1669b4c5d1b58438a1bc9742e52fcd63d`.
See [source hashes](evidence/SOURCE.json), the [prior-art audit](docs/PRIOR_ART.md)
and [Palomar handoff](docs/PALOMAR.md). The copied replay has only its import
paths adapted to this standalone layout. Mathematical evidence is retained.

JD Jones directs and maintains the project. Astra (OpenAI Codex) developed
the research and Lean formalization with parallel agent assistance. Grok's
credit for the original Analytic-Lab research station is preserved. Source
citations identify the published mathematical inputs; no peer combinatorial
implementation or investigation workflow was imported.

The repository is to remain **private**. JD will decide when to make it public
and will handle Palomar submission after the exact release is verified.
