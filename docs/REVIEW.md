# Pre-submission review disposition — October 7, 2026

The public submission package retains the sixteen verified principal
statements. The maintainer supplied a GPT-6 Pro review of
`d03ba898e7fd0d8102916bddb297eb35bf48fdea`; it reported no major correctness
defect in those statements. A fresh agent audit confirmed that the original
proof/build inputs still match the successful
[`c207efc` Linux verification](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572525271).
This is AI review and source-identity validation, not independent human peer
review or a new kernel replay.

## Incorporated findings

The supplementary [atom-geometry note](ATOM_GEOMETRY.md) gives the exact
maximum atom mass at every radius, the six-vertex simplex of small-radius
atom maximizers, the intersections of those faces, and consequences for
equality and exponents. Its mathematical arguments were checked separately.
The [exact rational checker](../evidence/atom_geometry.py) independently
constructs the trades, checks their balance and the dual coefficients,
verifies affine-family endpoints and the vertex incidence counts, and
rejects deliberately corrupted inputs. Run:

```sh
python3 evidence/atom_geometry.py
python3 -O evidence/atom_geometry.py
```

These supplementary results are outside the sixteen compared Lean claims.
The finite checks support the written proofs; they are not a kernel proof
of arbitrary-real-law statements. The optimal intermediate exponent curve,
worldwide novelty, and external human review remain unestablished.

The repository's current public, unsubmitted status and the separate review's
AI assistance are now recorded in the submission documentation and metadata.

## Deferred formal extension

The supplied patch proposed four Lean modules and five additional principal
statements. Actual checks with the pinned Lean toolchain found:

- `AtomBounds.lean:168`: exposed `middleAtomLaw` refers to private
  `middleAtomWeights`, followed by elaboration failures.
- `Holder.lean:54`: the proposed simplification fails with a transparency/type
  error (`function expected A y`).

The extension is a new formalization task, not a repair needed by the original
package. None of its Lean files, enlarged Challenge/Solution interfaces,
Comparator targets, or workflow changes were adopted. Their future inclusion
requires repaired compilation, axiom audits, statement comparison, and full
independent replay. The original sixteen statements and their verified proof
closure are unchanged.

## Provenance and branch state

Supplied archive: `four-row-pre-submission-review-2026-10-07.zip`.

- Archive SHA-256: `11589f590b15be0fe37fde59bfdcb49bc4be06963b2f9983abb650578d2c3f9f`.
- Supplied patch SHA-256: `29341fb2cccaee82a036e007a78c85ecc4e2e6fb6899a29c6654c33725c0b6d6`.
- Patch base: `d03ba898e7fd0d8102916bddb297eb35bf48fdea`.

The attachment's publishing instructions and claimed earlier approvals were
treated as review content. The maintainer's current request authorized this
repository update; submission remains their separate action.

The older `codex/formalization` tip
`ff07f4f897d4c190227eeee3f8f752788487dd3b` and `codex/release-verification`
tip `c207efc787a7e1c88aae29dc92d4be5e10297bf2` are already ancestors of the
reviewed main branch. They contain no missing formal work to merge and are
preserved. The separate verification-record branch and immutable tags also
remain intact. [VERIFICATION.md](VERIFICATION.md) and the
[review audit](../verification/review-2026-10-07.json) give the validation scope.
