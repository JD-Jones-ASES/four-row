# four-row

This is the separate Lean formalization of Analytic-Lab's four-row permanent
robustness handoff. JD authorized completing this private repository. Keep it
private; JD owns the later public release and Palomar submission.

Read README.md and the mathematical notes in docs/. Preserve the original
research evidence in evidence/ and its source provenance. Generated Lean
source is untrusted until checked by the kernel. No custom axioms, native
verification axioms, or proof holes may occur in the solution dependency graph.
Challenge holes are allowed only in the separate statement-of-record module.

Use the pinned toolchain and manifest. Keep generated certificate builds
bounded with the scripts in scripts/; this avoids exhausting memory. Verify
the exact final commit with private Linux CI, including statement comparison
and the independent kernels required by the current Palomar policy. Claim
only the exact principal theorems that pass those checks.

Use coherent codex/ branches and commits; no force-push. Do not import peer
combinatorial implementations or workflows. Canonical Mathlib and official
Lean/Palomar verification tools are permitted dependencies.
