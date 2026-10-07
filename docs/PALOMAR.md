> Imported research note from the Analytic-Lab source snapshot. Historical
> formalization and publication status below predates this spin-out; see
> [the project README](../README.md) for current checked coverage.

# Candidate: sharp robust permanent inequalities and entropy contraction

2026-10-06. Prepared at JD's request to consider a useful Palomar entry and
extend the surrounding mathematics. **Research candidate, not a submission
or a formalization project.** Lean development belongs in a separately
authorized spin-out. No claim of registry acceptance or worldwide novelty
follows from this assessment.

## Recommended mathematical package

Suggested title: **Sharp robustness and stability of the four-row permanent
inequality, with entropy contraction**.

The central result should be the sharp stability theorem, which organizes
the endpoint and strict-interior behavior in one statement. For balanced
\(\nu\) with \(d_{\rm TV}(\nu,u)\le r\le1/24\) and
\(\mathbb E_\mu f_i^2=1\),

\[
 1-\mathbb E_\nu\prod_i f_i(\sigma(i))
 \ge\frac{1-24r}{9}\sum_i\operatorname{Var}_\mu(f_i),
\]

with the coefficient optimal at each radius. The proposed principal claims are:

1. This sharp stability bound, its closed-endpoint consequence
   \(R_4(2)=1/24\), and the explicit extremizing/counterexample family.
2. Complete endpoint equality cases for nonnegative matrices.
3. The explicit exponent \(p(r)=2-(1-24r)/36\), and the exact threshold
   \(r<1/24\) for the existence of any uniform exponent below two.
4. The finite entropy inequality and sharp endpoint observation contraction;
   a general adaptive tensorization lemma makes the result reusable.

These have complete Lab proofs in [ENDPOINT](ENDPOINT.md) and
[EXTENSIONS](EXTENSIONS.md). A future entry must list only the principal
claims actually formalized and independently audited. The explicit interior
exponent is not advertised as optimal. Rectangles, concentration and
conditional-resampling estimates can be derivations in an accompanying note;
if advertised as formal principal claims they also need audited Lean theorems.

The research-interest case is the exact perturbation threshold and sharp
stability for a nonuniform permutation law, beyond the uniform theory and the
qualitative robustness in the [direct predecessor](PRIOR_ART.md). The intended
audience is finite functional inequalities, probability and permanents.
Formal proof length and certificate size are not the interest argument.

## Concrete statement and dependency plan

An algebraic endpoint statement can avoid square roots. For
\(\nu:S_4\to\mathbb R_{\ge0}\), require total mass one, all sixteen
marginal sums equal \(1/4\), and
\(\sum_\sigma|\nu(\sigma)-1/24|\le1/12\). For every \(A\ge0\), conclude

\[
 256\left(\sum_\sigma\nu(\sigma)\prod_i a_{i,\sigma(i)}\right)^2
 \le\prod_i\sum_j a_{ij}^2.
\]

This is exactly the probability-row-\(L^2\) statement, including zero rows.
The normalized stability theorem is also algebraic:
\(\frac14\sum_j a_{ij}^2=1\) and
\(\operatorname{Var}_\mu(a_i)=1-(\frac14\sum_j a_{ij})^2\).
No rational-law restriction, strict-radius substitution, or positivity of
every matrix entry may silently replace the real closed-ball theorem.

Suggested dependency order:

1. Finite permutation indexing, incidence matrix and balanced signed laws.
2. A reusable finite sign-compatible circuit decomposition lemma, then the
   complete support enumeration and row/column symmetry coverage.
3. A proved rational Gram-certificate checker, coefficient expansion, and
   positive-definiteness evidence for every representative.
4. Row normalization, all-law transfer, sharpness and equality.
5. The short scalar quartic identity, pair estimate and uniform deficit;
   mixing with the endpoint then proves the sharp stability theorem.
6. Finite \(L^p\) norm differentiation for the explicit exponent; finite
   entropy duality and conditional iteration for the applications.

The analytic lemmas in step 6 should be generic and reusable. They add
formalization work beyond a finite SOS check, but make a stronger entry than
an isolated machine-checked numerical threshold. The endpoint and stability
proofs do not require formalizing Bristiel–Caputo's general theorem.

An elementary replacement for abstract polytope theory is available. For a
nonzero real \(x\in\ker B\), choose a nonzero kernel vector \(y\) supported
inside \(\operatorname{supp}x\), with the same signs on its nonzero coordinates
and minimum support. If a proper sub-support
supports a nonzero kernel vector \(z\), choose its orientation and subtract
\(t z\) from \(y\), where \(t\) is the minimum positive ratio that makes
a coordinate vanish. This preserves signs and leaves a nonzero coordinate
outside \(\operatorname{supp}z\), a contradiction. Thus \(y\) is a circuit.
Subtract from \(x\) the largest sign-compatible multiple of \(y\); the
residual has smaller support and the \(\ell^1\) norms add. Induction expresses
\(x\) as a nonnegative sum of conformal circuits. Normalizing each circuit
to norm two gives coefficients summing to \(\|x\|_1/2\le1\). The remaining
coefficient goes on zero, the midpoint of any opposite circuit pair.
The circuit's one-dimensional real kernel is generated by its primitive
rational vector, so the finite rational census covers it. This removes a
convex-polytope library dependency without weakening the theorem.

## Certificate and verification burden

[P0182](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/a763c72511bef8bb915449576581222a9dc1fb05/probes/P0182_permanent_robustness/NOTES.md) has 73 support orbits,
131 oriented representatives and 48,368 labelled signed vertices. The exact
Gram payload is 1,195,150 bytes, with 13,744 positive rational pivots and
maximum saved entry denominator 504,000. Only five distinct basis matrices
occur. A scratch lossless schema experiment reduced the payload to about
239 kB by sharing bases and storing symmetric rational matrices compactly;
the largest exact LDL numerator/denominator seen had 136/141 bits. That
experiment is a feasibility observation, not a changed or verified release
format. The durable evidence remains the original JSON and literal checker.

The main risk is proving **complete census coverage and the real all-law
reduction**, not merely reading 131 certificates. A Lean program that accepts
the supplied JSON without a proved soundness and coverage theorem would not
formalize the claim. Python and solver output cannot be axioms. Benchmark a
kernel-checked certificate path and census proof before promising a short
formalization. No Lean implementation or timing experiment has been done.

## Policy and handoff

The [official policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md)
was checked on October 6 at commit
`96b034cc31a72a63d4f4041911dce337a85c9a04`. It requires a substantive
research-interest case as well as verified correctness. Principal claims
must match the audited statement. An eventual public, committed Lean package
needs Comparator and NanoDa verification on its exact release; generated
certificates belong in the package, and `Lean.ofReduceBool` is not an allowed
axiom. Source-origin and AI-disclosure metadata must reflect actual provenance.
Recheck the policy when a spin-out is authorized.

The established [Lab workflow](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/a763c72511bef8bb915449576581222a9dc1fb05/docs/WORKFLOW.md#palomar-ready-spin-outs)
keeps research here until a separate project is requested, and release and
submission are separate actions. This note completes the requested assessment;
it does not initiate any of those later actions.

The immutable endpoint evidence is commit
`c054cfc1669b4c5d1b58438a1bc9742e52fcd63d`. The extension's exact snapshot and
actual validation are recorded in the
[applications session log](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/a763c72511bef8bb915449576581222a9dc1fb05/research/log/2026-10-06-permanent-applications.md).
Use that snapshot, the full source audit, the exact replay commands, and the
explicit list of unresolved questions when preparing an eventual extraction.
