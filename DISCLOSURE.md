# Assistance and review

OpenAI GPT-6 Astra agents, working through OpenAI Codex, developed the
mathematical arguments, exact certificates, Lean proofs, and documentation
under the responsible maintainer's direction. Parallel agents worked on
separate proof components and reviewed theorem scope, definitions, census
coverage, and the assembled formalization.

The endpoint and extension source notes in docs/ were prepared before the
Lean development and are included as its source account. The formalization proves the sixteen
statements listed in docs/THEOREMS.md. The supplementary local-exponent note
and additional application consequences are distinguished from that scope.
Published antecedents are credited in docs/PRIOR_ART.md and formalization.yaml.

Python generated finite witness data and proof source using exact arithmetic.
Lean proves the checks and their soundness. The complete exported proof
passed con-ron, NanoDa, and Lean kernel replay at the commit recorded in
docs/VERIFICATION.md; neither AI output nor Python output is a proof axiom.

The maintainer supplied a separate GPT-6 Pro review dated October 7, 2026.
It reported no major correctness defect in the original sixteen statements
and proposed additional atom geometry and five uncompiled Lean statements.
GPT-6 Astra agents checked its mathematics and exact finite evidence,
confirmed compilation failures in two candidate modules, and retained the
new geometry as supplementary mathematics. The candidate Lean additions
are not in the submitted proof graph or Comparator contract.
[REVIEW.md](docs/REVIEW.md) records the scope and disposition.

Review was by AI agents. No independent human expert review,
source-author endorsement, or worldwide-priority claim is recorded.
Mechanical checking establishes the recorded formal statements under their
axioms; it does not establish research significance or novelty.

Human authorship and maintenance responsibility are recorded in
[formalization.yaml](formalization.yaml). Detailed prompt and cost accounting
was not retained as part of this repository.
