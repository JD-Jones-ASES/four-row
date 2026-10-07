# four-row

Read README.md, docs/THEOREMS.md, and docs/VERIFICATION.md before changing
the formalization. Keep the repository private until the maintainer explicitly
authorizes a visibility change. Submission is a separate maintainer action.

Preserve the exact scope of the sixteen principal theorems and the research
evidence in evidence/. Generated Lean source is untrusted until checked by
the kernel. No custom axioms, native verification axioms, or proof holes may
occur in the Solution dependency graph. Challenge holes belong only in the
separate statement-of-record module.

Use the pinned toolchain and manifest. Keep certificate compilation bounded
with the existing scripts and import chains. Mathematical, dependency,
Comparator, or executable build/generator changes require the complete Lean
build, axiom audit, statement comparison, and independent kernel replay on
the changed source. State the exact checked commit and scope.

For documentation and metadata changes, validate the current metadata
contract, check links and scope, and establish that proof/build inputs are
unchanged from the verified commit. Do not report this as a new complete
kernel replay or repeat the census solely for prose changes.

Keep the documentation focused on mathematics, reproducibility, and necessary
attribution. Record AI assistance in DISCLOSURE.md and formalization.yaml.
Keep personal names in authorship, responsibility, or bibliographic fields.

Use coherent codex/ branches unless the maintainer requests main directly;
no force-push. Preserve historical evidence and tags. Do not import peer
combinatorial implementations or workflows. Canonical Mathlib and official
Lean/Palomar verification tools are permitted dependencies.
