# Palomar submission details

## Package

| Field | Value |
|---|---|
| Title | Sharp robustness and stability of the four-row permanent inequality |
| Repository | `JD-Jones-ASES/four-row` |
| Project directory | Repository root |
| Metadata | `formalization.yaml` |
| Comparator configuration | `comparator.json` |
| Challenge / Solution | `FourRowChallenge` / `FourRowSolution` |
| Selected statements | The sixteen `FourRowPrincipal` declarations in `comparator.json` |
| License | MIT |

Use the full 40-character commit returned by `git rev-parse HEAD` on the
intended `main` checkout. A branch name or tag is not a submission revision.
The repository is public and has not been submitted as of October 7, 2026.
The sixteen-statement package is prepared for maintainer submission; any
later registration remains a separate outcome.

## Mathematical account

The package formalizes the sharp balanced-law robustness radius $1/24$, the
optimal variance-deficit coefficient $(1-24r)/9$, complete endpoint equality
cases, an explicit extremal family, and exponent and entropy consequences.
It includes adaptive tensorization under conditional assumptions on every
positive-probability full permutation history.

The research-interest case is the exact perturbation threshold and sharp
stability for nonuniform permutation laws, beyond the uniform permanent
inequality and the qualitative robustness of the direct predecessor. The
intended audience is permanent inequalities, finite functional inequalities,
and probability. [Prior art](PRIOR_ART.md) records the comparison and its limits.

[THEOREMS.md](THEOREMS.md) maps every selected declaration to its informal
statement. The explicit interior exponent is sufficient, not optimal.
The [review disposition](REVIEW.md) retains these sixteen statements.
The later [atom-geometry note](ATOM_GEOMETRY.md) is supplementary and its
proposed five Lean additions are excluded from the submission contract.
Supplementary notes include further informal consequences; a global shuffle
mixing theorem is outside the formal claim. The source account is included
in [ENDPOINT.md](ENDPOINT.md) and [EXTENSIONS.md](EXTENSIONS.md).

## Requirements checked on October 7, 2026

The current official repository heads are unchanged from the proof audit:

- [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md): `96b034cc31a72a63d4f4041911dce337a85c9a04`.
- [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44): `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.

The package uses `formalization.yaml` v0.4 with a mathematical abstract,
human authorship and responsible maintenance, classification, explicit source
relationships, automation disclosure, and completed-review status. Its origin
remains source-based: it formalizes the mathematical notes included here.
The repository contains the substantive Lean development and is not a wrapper
around a separate proof project.

The pinned Lean `v4.35.0-rc3` meets the current minimum `v4.35.0-rc2`.
All Lean files use the module system and meet the 10,000-line limit. The
Mathlib-only Challenge meets its separate 1,000-line and 100-KiB limits,
and its module name does not shadow a dependency. Dependencies are pinned
to full Git commit hashes, and the root MIT license matches the metadata.

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. Intentional
Challenge theorem holes are separate from the proved Solution. Palomar
supplies its own protected configuration for independent kernel replay;
the submitted Comparator configuration contains no `external_kernels` field.

[Verification](VERIFICATION.md) records the completed proof replay and the
checks for this documentation revision. The private-runner cold build is not
an official Palomar hardware-profile preflight. Palomar performs its own
exact-commit mechanical checks and editorial review; no registry outcome is
claimed here.
