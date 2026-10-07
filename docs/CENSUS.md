# Proof-carrying support census

The formal all-law reduction does not trust a Python rank calculation, a
floating-point solver, the census counts, or a modular-rank shortcut.

`FourRow.Census.extension_coverage` proves the following finite combinatorial
lemma. Start with a listed empty independent support. Suppose every extension
of every listed independent support by one coordinate is either a relabeling
of another listed independent support or contains a relabeling of a listed
circuit support. Then every finite support is either a relabeling of a listed
independent support or contains a relabeling of a listed circuit support.
The proof is induction on finite sets; all relabelings are members of the
actual row/column permutation group.

The generated tables contain 5,109 independent support representatives,
including the empty support, and 73 nonzero integer kernel vectors. They
supply an explicit row/column action for every support extension. Each
extension identity or containment is checked in Lean's kernel. Both the
permutation order and every incidence entry are literal definitions.

Only the 1,282 maximal independent supports require linear-algebra
certificates. Each certificate supplies selected incidence rows and an
integer matrix `L` satisfying `L B = d I` with nonzero integer `d`. The generic
`integer_left_inverse` theorem transfers this identity to real column
independence. Every smaller listed independent support has a checked
embedding into a relabeling of one of these maximal supports. No inference
from modular arithmetic is necessary.

Apply the finite coverage lemma to the support of a nonzero real balanced
signed law. The independent alternative contradicts its kernel equations.
Consequently its support contains a relabeling of one of the 73 nonzero
integer kernel vectors. This is the exact interface used by the generic
compact-convex reduction in `FourRow.Circuit`: at an extreme point, every
contained kernel vector must be proportional to the point. Normalized
positive and negative circuit orientations are then matched to the rational
Gram certificates.

The Python generators are untrusted producers of finite witnesses. The
Lean tables use `decide +kernel`, not `native_decide` or `Lean.ofReduceBool`.
Regeneration, followed by a successful Lean build, is a replay of the proof;
regeneration by itself is not.

Replay the proof-carrying data from the packaged P0182 source evidence:

```sh
python3 scripts/generate_census_certificate.py \
  --source evidence \
  --output evidence/support-closure.json
python3 scripts/emit_census_tables.py
python3 scripts/emit_census_proofs.py
python3 scripts/build_census.py
```

The sequential build runner keeps certificate verification within a bounded
memory footprint; ordinary `lake build` checks the same declarations.
