module

public import FourRow.Definitions

@[expose] public section

namespace FourRow
open scoped BigOperators

/-- The balanced identity/derangement/transposition trade, in lexicographic order. -/
def sharpTrade : PermIndex → ℚ := ![
  1/2, -1/6, -1/6, 0, 0, -1/6,
  -1/6, 1/18, 0, 1/18, 1/18, 0,
  0, 1/18, -1/6, 0, 1/18, 1/18,
  1/18, 0, 0, -1/6, 1/18, 1/18]

theorem sharpTrade_mass : (∑ p : PermIndex, sharpTrade p) = 0 := by
  norm_num [sharpTrade, Fin.sum_univ_succ]

theorem sharpTrade_abs : (∑ p : PermIndex, |sharpTrade p|) = 2 := by
  norm_num [sharpTrade, Fin.sum_univ_succ]

theorem sharpTrade_marginal (i j : Row) :
    (∑ p : PermIndex, if permutation p i = j then sharpTrade p else 0) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpTrade, permutation, Fin.sum_univ_succ]

/-- A real balanced law with exactly prescribed TV distance for 0 ≤ δ ≤ 1/4. -/
noncomputable def sharpLaw (δ : ℝ) : Law := fun σ =>
  1/24 + δ * (sharpTrade (lexEquiv.symm σ) : ℝ)

theorem sum_lex (f : Perm4 → ℝ) : (∑ σ, f σ) = ∑ p, f (lexEquiv p) := by
  exact (Equiv.sum_comp lexEquiv f).symm

private theorem sharpTrade_mass_real : (∑ p : PermIndex, (sharpTrade p : ℝ)) = 0 := by
  exact_mod_cast sharpTrade_mass

private theorem sharpTrade_abs_real : (∑ p : PermIndex, |(sharpTrade p : ℝ)|) = 2 := by
  exact_mod_cast sharpTrade_abs

theorem sharpLaw_probability (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/4) :
    Probability (sharpLaw δ) := by
  constructor
  · intro σ
    obtain ⟨p, rfl⟩ := lexEquiv.surjective σ
    simp only [sharpLaw, Equiv.symm_apply_apply]
    fin_cases p <;> norm_num [sharpTrade] <;> linarith
  · rw [sum_lex]
    simp [sharpLaw, Finset.sum_add_distrib, ← Finset.mul_sum, sharpTrade_mass_real]


theorem sharpLaw_balanced (δ : ℝ) : Balanced (sharpLaw δ) := by
  intro i j
  rw [sum_lex]
  change (∑ p : PermIndex, if permutation p i = j then
    1/24 + δ * (sharpTrade p : ℝ) else 0) = 1/4
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpTrade, permutation, Fin.sum_univ_succ] <;> ring

theorem sharpLaw_distance (δ : ℝ) (hδ : 0 ≤ δ) : tvDistance (sharpLaw δ) = δ := by
  unfold tvDistance
  rw [sum_lex]
  simp only [sharpLaw, uniformLaw, Equiv.symm_apply_apply, add_sub_cancel_left,
    abs_mul, abs_of_nonneg hδ]
  rw [← Finset.mul_sum, sharpTrade_abs_real]
  ring

theorem sharpLaw_inBall (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/4) :
    InBall (sharpLaw δ) δ :=
  ⟨sharpLaw_probability δ hδ hδ', sharpLaw_balanced δ,
    le_of_eq (sharpLaw_distance δ hδ)⟩

/-- Matching singleton rows, normalized for the uniform four-point measure. -/
def sharpRows : Rows := fun i j => if i = j then ((2 : ℕ) : ℝ) else 0

theorem sharpRows_nonnegative : NonnegativeRows sharpRows := by
  intro i j
  simp only [sharpRows]
  split_ifs <;> norm_num

theorem sharpRows_normalized : NormalizedRows sharpRows := by
  intro i
  fin_cases i <;> norm_num [sharpRows, Fin.sum_univ_succ]

theorem sharpRows_variance : varianceSum sharpRows = 3 := by
  norm_num [varianceSum, sharpRows, Fin.sum_univ_succ]

theorem sharpLaw_expectation (δ : ℝ) : expectation (sharpLaw δ) sharpRows = 2/3 + 8*δ := by
  unfold expectation
  rw [sum_lex]
  change (∑ p : PermIndex, (1/24 + δ * (sharpTrade p : ℝ)) *
    ∏ i : Row, sharpRows i (permutation p i)) = 2/3 + 8*δ
  norm_num [sharpTrade, sharpRows, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- No coefficient larger than the advertised sharp coefficient is valid. -/
theorem stability_coefficient_le (r κ : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/24)
    (h : ∀ ν, InBall ν r → ∀ A, NonnegativeRows A → NormalizedRows A →
      κ * varianceSum A ≤ 1 - expectation ν A) :
    κ ≤ (1 - 24*r)/9 := by
  have hball := sharpLaw_inBall r hr (by linarith : r ≤ 1/4)
  have hsharp := h (sharpLaw r) hball sharpRows sharpRows_nonnegative sharpRows_normalized
  rw [sharpRows_variance, sharpLaw_expectation] at hsharp
  linarith

/-- Every radius larger than 1/24 admits an actual balanced counterexample. -/
theorem counterexample_above_endpoint (r : ℝ) (hr : 1/24 < r) :
    ∃ ν : Law, ∃ A : Rows, InBall ν r ∧ NonnegativeRows A ∧ NormalizedRows A ∧
      1 < expectation ν A := by
  let δ := min ((r + 1/24)/2) (1/8)
  have hdlo : 1/24 < δ := by
    dsimp [δ]
    apply lt_min <;> linarith
  have hdhi : δ ≤ 1/4 := le_trans (min_le_right _ _) (by norm_num)
  have hdr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd0 : 0 ≤ δ := by linarith
  have hball := sharpLaw_inBall δ hd0 hdhi
  refine ⟨sharpLaw δ, sharpRows, ?_, sharpRows_nonnegative, sharpRows_normalized, ?_⟩
  · exact ⟨hball.probability, hball.balanced, hball.distance.trans (le_of_lt hdr)⟩
  · rw [sharpLaw_expectation]
    linarith

end FourRow
