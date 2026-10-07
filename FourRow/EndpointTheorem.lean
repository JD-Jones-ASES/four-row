import FourRow.CertificateTransfer
import FourRow.CensusCoverage
import FourRow.Grams
import FourRow.EqualityEndpoint

/-!
# The certified four-row endpoint

The final theorems have no census, SOS, rationality, or positivity hypotheses
beyond the human-facing balanced probability law and nonnegative matrix.
-/
namespace FourRow
noncomputable section

/-- Full real closed-ball quartic bound, including the explicit positive defect.
Both the exhaustive support cover and all 131 Gram identities are proved in
Lean and enter this theorem as theorems, never as trusted input data. -/
theorem strongQuarticBound : StrongQuarticBound :=
  strongQuarticBound_of_gram_cover Census.support_cover gram_defect_bound

/-- The central normalized four-row endpoint. -/
theorem endpointBound : EndpointBound :=
  endpointBound_of_quarticBound strongQuarticBound.quarticBound

/-- Square-root-free four-row endpoint for arbitrary nonnegative real entries,
including every zero-row boundary case. -/
theorem endpoint_algebraic (ν : Law) (hν : InBall ν (1/24))
    (A : Rows) (hA : NonnegativeRows A) :
    256 * (expectation ν A)^2 ≤ ∏ i : Row, ∑ j : Row, A i j ^ 2 :=
  endpoint_algebraic_of_bound endpointBound ν hν A hA

/-- Exact normalized endpoint equality classification. -/
theorem normalized_endpoint_equality
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A)
    (hn : NormalizedRows A) :
    expectation ν A = 1 ↔
      (∀ i j, A i j = 1) ∨
      (∃ τ : Perm4, (∀ i j, A i j = if j = τ i then 2 else 0) ∧ ν τ = 1/16) :=
  normalized_endpoint_equality_of_strong strongQuarticBound ν hν A hA hn

/-- Complete nonnegative equality classification with arbitrary row scalings. -/
theorem endpoint_algebraic_equality
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256 * (expectation ν A)^2 = (∏ i : Row, ∑ j : Row, A i j ^ 2) ↔
      EndpointEqualityShape ν A :=
  endpoint_algebraic_equality_of_strong strongQuarticBound ν hν A hA

end
end FourRow
