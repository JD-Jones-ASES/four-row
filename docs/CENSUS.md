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

Supports are encoded as 24-bit natural numbers. A proved bitwise-image lemma
connects each numeric action check to the corresponding finite-set image;
bitwise intersection proves containment. The checker skips an extension by a
coordinate already present, because that extension is the original support.
Binary lookup trees keep reduction logarithmic in the table size. These
representations affect checking cost, without adding a trusted computation.

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
CI uses `scripts/build_census_shard.py --shard 0 --shards 1` for the full
census chain, followed by the sequential runner to assemble and check the
semantic coverage proof. Private predecessor imports enforce this ordering
also during a direct cold Solution build. Splitting the census into more
shards repeats prerequisite work and is no longer the recommended route.

## Scoped verification record

[`verification/census.json`](../verification/census.json) records the successful
eight-shard Linux check of all 81 certificate leaves at
`5ac56b66b910c536ff52fa4b1dc2443d41f5de99`, with clean-commit flags on every
shard. The completed semantic assembly matches
`4c11ca43afd49c1b3b1a0562e0e3acbc33e8c8a5`. Its principal census theorems use
only `propext`, `Classical.choice`, and `Quot.sound`.

The complete dependency closure of `FourRow.Census.support_cover` was exported
and checked locally by both bundled independent kernels:

| Checker | Result | Wall time | Maximum RSS |
| --- | --- | --- | --- |
| NanoDa, serial | 14,966 declarations; no type-checking errors | 922.39 s | 3.70 GB |
| con-ron, verified, two workers | 13,492 checks completed; 13,949 declarations accepted | 667.09 s | 7.82 GB |

These are macOS measurements from `time -l`, with decimal GB. NanoDa exited
successfully and separately reported the pretty-printer message “Unable to
print axioms”; the Lean axiom audit passed. Both checkers read the same
86,558,045-byte export, whose hash is recorded in the JSON. Checker declaration
counts use their respective reporting conventions.

The two-worker con-ron run exceeded a standard private Linux runner's memory
budget. Production verification uses one worker per independent checker and
provides swap headroom. Its Linux resource use is a separate measurement.
This record verifies the census only. The complete release still requires
the full theorem closure, statement comparison, and the checks described in
[`VERIFICATION.md`](VERIFICATION.md).
