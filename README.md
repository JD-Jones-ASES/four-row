# four-row

A private formalization of sharp robustness and stability for the four-row
permanent inequality, based on Analytic-Lab's October 6, 2026 handoff.

**Development in progress. This snapshot is not yet submission-ready.**
The full mathematical research result is proved by exact computer-assisted
arguments in [the endpoint note](docs/ENDPOINT.md) and
[the extensions](docs/EXTENSIONS.md). The Lean development is separate from
that evidence and must prove the full real-law coverage before claiming the
endpoint theorem. No publication or Palomar submission has been made.

For every balanced real probability law on the 24 permutations within total
variation distance `r ≤ 1/24` of uniform, and nonnegative rows normalized in
probability L², the intended principal theorem is

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
lake exe cache get
python3 scripts/build_grams.py --jobs 3
lake build
```

`lean-toolchain` and `lake-manifest.json` pin Lean and all dependencies.
The generated Gram modules contain explicit rational sum-of-squares proofs;
Python generates source text, while Lean checks the polynomial identities.
The generation script and original certificate data are committed.

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
