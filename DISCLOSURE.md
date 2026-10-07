# Assistance and review

OpenAI GPT-6 Astra agents, working through OpenAI Codex, developed the
mathematical arguments, exact certificates, Lean proofs, and documentation
under the responsible maintainer's direction. Parallel agents worked on
separate proof components and reviewed theorem scope, definitions, census
coverage, and the assembled formalization.

The mathematical notes in docs/ were prepared before the Lean development
and are included as its source account. The formalization proves the sixteen
statements listed in docs/THEOREMS.md. The supplementary local-exponent note
and additional application consequences are distinguished from that scope.
Published antecedents are credited in docs/PRIOR_ART.md and formalization.yaml.

Python generated finite witness data and proof source using exact arithmetic.
Lean proves the checks and their soundness. The complete exported proof
passed con-ron, NanoDa, and Lean kernel replay at the commit recorded in
docs/VERIFICATION.md; neither AI output nor Python output is a proof axiom.

Review was internal agent review. No independent human expert review,
source-author endorsement, or worldwide-priority claim is recorded.
Mechanical checking establishes the recorded formal statements under their
axioms; it does not establish research significance or novelty.

Human authorship and maintenance responsibility are recorded in
[formalization.yaml](formalization.yaml). Detailed prompt and cost accounting
was not retained as part of this repository.
