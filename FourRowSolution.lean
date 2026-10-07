module

public import FourRow.EndpointTheorem
public import FourRow.ExtremalFamily
public import FourRow.SharpExponent
public import FourRow.SharpEntropy
public import FourRow.EntropyExponent
public import FourRow.NormMonotonicity
public import FourRow.Tensorization

@[expose] public section

/-! Closed proofs of every standalone FourRowChallenge principal statement.
This module does not import the challenge, and introduces no proof holes. -/
open FourRow
namespace FourRowPrincipal
noncomputable section

/-- The exact closed endpoint, without square roots and including zero rows. -/
theorem endpoint (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256*(expectation ν A)^2 ≤ ∏ i : Row, ∑ j : Row, A i j^2 := by exact FourRow.endpoint_algebraic ν hν A hA

/-- The sharp stability coefficient throughout the closed balanced ball. -/
theorem sharp_stability (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) (hn : NormalizedRows A) :
    ((1-24*r)/9)*varianceSum A ≤ 1-expectation ν A := by exact FourRow.stability_of_endpoint FourRow.endpointBound ν r hr hrmax hν A hA hn

/-- Every coefficient valid on the entire ball is at most the stated one. -/
theorem stability_optimal (r κ : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (h : ∀ ν, InBall ν r → ∀ A, NonnegativeRows A → NormalizedRows A →
      κ*varianceSum A ≤ 1-expectation ν A) : κ ≤ (1-24*r)/9 := by exact FourRow.stability_coefficient_le r κ hr hrmax h

/-- The explicit balanced family has exact TV distance and matching-row value. -/
theorem explicit_extremal_family (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/4) :
    InBall (extremalLaw r) r ∧ tvDistance (extremalLaw r) = r ∧
    NonnegativeRows sharpRows ∧ NormalizedRows sharpRows ∧ varianceSum sharpRows = 3 ∧
    expectation (extremalLaw r) sharpRows = 2/3+8*r := by exact FourRow.extremal_family r hr hrmax

/-- Every larger radius contains an actual balanced normalized counterexample. -/
theorem radius_sharp (r : ℝ) (hr : 1/24 < r) :
    ∃ ν : Law, ∃ A : Rows, InBall ν r ∧ NonnegativeRows A ∧ NormalizedRows A ∧
      1 < expectation ν A := by exact FourRow.counterexample_above_endpoint r hr

/-- All equality cases, including arbitrary nonnegative row scales and zero rows. -/
theorem endpoint_equality (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256*(expectation ν A)^2 = (∏ i : Row, ∑ j : Row, A i j^2) ↔
      EndpointEqualityShape ν A := by exact FourRow.endpoint_algebraic_equality ν hν A hA

/-- The sufficient exponent p(r) for every nonnegative matrix. -/
theorem explicit_exponent (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) (explicitExponent r) := by exact FourRow.explicitExponent_bound FourRow.endpointBound ν r hr hrmax hν A hA

/-- Every exponent at least p(r) also satisfies the row-product inequality. -/
theorem larger_exponents (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24) (hν : InBall ν r)
    (A : Rows) (hA : NonnegativeRows A) (p : ℝ) (hp : explicitExponent r ≤ p) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) p := by exact FourRow.largerExponent_bound FourRow.endpointBound ν r hr hrmax hν A hA p hp

/-- An exponent strictly below two works uniformly exactly at interior radii. -/
theorem subcritical_threshold (r : ℝ) (hr : 0 ≤ r) :
    (∃ p : ℝ, 1 ≤ p ∧ p < 2 ∧ ∀ ν, InBall ν r → ∀ A, NonnegativeRows A →
      expectation ν A ≤ ∏ i : Row, powerNorm (A i) p) ↔ r < 1/24 := by exact FourRow.subcritical_exponent_iff FourRow.endpointBound r hr

/-- The finite entropy inequality, including infinite relative-entropy cases. -/
theorem entropy (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (marginalEntropySum ρ : EReal) ≤ (explicitExponent r : EReal)*relativeEntropy ρ ν := by exact FourRow.explicitExponent_entropy FourRow.endpointBound ν ρ r hr hrmax hν hρ

/-- A uniformly sampled row/image observation contracts entropy by p(r)/4. -/
theorem observation_contraction (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (finiteKL (observationLaw ρ) (observationLaw ν) : EReal) ≤
      ((explicitExponent r/4:ℝ):EReal)*relativeEntropy ρ ν := by exact FourRow.explicitExponent_observation_entropy FourRow.endpointBound ν ρ r hr hrmax hν hρ

/-- The endpoint entropy coefficient two is optimal over the balanced ball. -/
theorem entropy_optimal (κ : ℝ)
    (h : ∀ ν, InBall ν (1/24) → ∀ ρ, Probability ρ → Supports ρ ν →
      marginalEntropySum ρ ≤ κ*finiteKL ρ ν) : 2 ≤ κ := by exact FourRow.entropy_coefficient_ge_two κ h

/-- The endpoint observation coefficient one half is optimal over the ball. -/
theorem observation_optimal (κ : ℝ)
    (h : ∀ ν, InBall ν (1/24) → ∀ ρ, Probability ρ → Supports ρ ν →
      finiteKL (observationLaw ρ) (observationLaw ν) ≤ κ*finiteKL ρ ν) : 1/2 ≤ κ := by
  have hsharp : 2 ≤ 4*κ := FourRow.entropy_coefficient_ge_two (4*κ) (by
    intro ν hν ρ hρ hs
    have hh := h ν hν ρ hρ hs
    rw [FourRow.observationLaw_of_balanced ν hν.balanced,
      FourRow.observation_entropy_identity] at hh
    linarith only [hh])
  linarith only [hsharp]

/-- The same exponent tensorizes under arbitrary full-history dependence. -/
theorem adaptive_tensorization (K : StepKernels) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (n : ℕ) (hK : Admissible K r n) (F : Row → RowHistory n → ℝ)
    (hF : ∀ i x, 0 ≤ F i x) :
    (∑ h : PermHistory n, pathWeight K n h*∏ i : Row, F i (rowHistory i n h)) ≤
      ∏ i : Row, historyNorm n (F i) (explicitExponent r) := by exact FourRow.explicitExponent_tensorization FourRow.endpointBound K r hr hrmax n hK F hF

/-- Admissible adaptive kernels define a genuine probability law on paths. -/
theorem adaptive_probability (K : StepKernels) (r : ℝ) (n : ℕ) (hK : Admissible K r n) :
    (∀ h, 0 ≤ pathWeight K n h) ∧ (∑ h, pathWeight K n h) = 1 := by
  have hp := fun t ht h hh => (hK t ht h hh).probability
  exact ⟨FourRow.pathWeight_nonneg K n hp,FourRow.pathWeight_mass K n hp⟩

/-- Each individual row path is uniform product measure, even for adaptive kernels. -/
theorem adaptive_marginals (K : StepKernels) (r : ℝ) (n : ℕ) (hK : Admissible K r n)
    (i : Row) (F : RowHistory n → ℝ) :
    (∑ h : PermHistory n, pathWeight K n h*F (rowHistory i n h)) =
      (∑ x : RowHistory n, F x)/(4:ℝ)^n := by exact FourRow.rowHistory_expectation K r n hK i F

end
end FourRowPrincipal
