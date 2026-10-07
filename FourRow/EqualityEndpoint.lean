import FourRow.Equality
import FourRow.Normalization

namespace FourRow
noncomputable section

/-- A permutation-supported matrix has one surviving permutation monomial. -/
theorem expectation_permutation_rows (ν : Law) (τ : Perm4) (d : Row → ℝ) :
    expectation ν (fun i j => if j = τ i then d i else 0) = ν τ * ∏ i, d i := by
  classical
  unfold expectation
  rw [Finset.sum_eq_single τ]
  · simp
  · intro σ _ hσ
    have hne : ∃ i : Row, σ i ≠ τ i := by
      by_contra h
      push Not at h
      exact hσ (Equiv.ext h)
    obtain ⟨i, hi⟩ := hne
    have hp : (∏ j : Row, if σ j = τ j then d j else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hp]
  · simp

/-- Complete equality classification for normalized nonnegative matrices,
conditional only on the strong endpoint that the exact census proves. -/
theorem normalized_endpoint_equality_of_strong (hstrong : StrongQuarticBound)
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A)
    (hn : NormalizedRows A) :
    expectation ν A = 1 ↔
      (∀ i j, A i j = 1) ∨
      (∃ τ : Perm4, (∀ i j, A i j = if j = τ i then 2 else 0) ∧ ν τ = 1/16) := by
  constructor
  · intro he
    have hd := defect_zero_of_endpoint_equality hstrong ν hν A hn he
    rcases normalized_product_classification A hA hn (productRelations_of_defect_zero A hd)
      with hconst | ⟨τ,hperm⟩
    · exact Or.inl hconst
    · right
      refine ⟨τ,hperm,?_⟩
      have hfun : A = fun i j => if j = τ i then 2 else 0 := funext fun i => funext (hperm i)
      have hh := expectation_permutation_rows ν τ (fun _ => 2)
      rw [← hfun, he] at hh
      norm_num at hh
      linarith
  · rintro (hconst | ⟨τ,hperm,hmass⟩)
    · simpa [expectation, hconst] using hν.probability.mass
    · have hfun : A = fun i j => if j = τ i then 2 else 0 := funext fun i => funext (hperm i)
      rw [hfun, expectation_permutation_rows, hmass]
      norm_num

/-- Matrix-side equality shapes; zero rows are retained as a separate complete
boundary case. All entries are nonnegative in the theorem using this predicate. -/
def EndpointEqualityShape (ν : Law) (A : Rows) : Prop :=
  (∃ i : Row, ∀ j : Row, A i j = 0) ∨
  (∃ c : Row → ℝ, ∀ i j, A i j = c i) ∨
  (∃ τ : Perm4, ν τ = 1/16 ∧
    ∀ i j, A i j = if j = τ i then A i (τ i) else 0)

/-- Complete endpoint equality, including zero rows and arbitrary positive row
rescalings of the normalized cases. -/
theorem endpoint_algebraic_equality_of_strong (hstrong : StrongQuarticBound)
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256 * (expectation ν A)^2 = (∏ i : Row, ∑ j : Row, A i j ^ 2) ↔
      EndpointEqualityShape ν A := by
  constructor
  · intro he
    by_cases hz : ∃ i : Row, rowSquareSum A i = 0
    · obtain ⟨i,hi⟩ := hz
      exact Or.inl ⟨i, zero_row_of_squareSum A i hi⟩
    · have hz' : ∀ i : Row, rowSquareSum A i ≠ 0 := fun i hi => hz ⟨i,hi⟩
      obtain ⟨s,B,hs,hBn,hBN,hAB,hprod⟩ := exists_row_normalization A hA hz'
      have hBE := normalized_expectation_eq_one ν hν.probability A B hBn s hs hAB hprod he
      rcases (normalized_endpoint_equality_of_strong hstrong ν hν B hBn hBN).mp hBE
        with hconst | ⟨τ,hperm,hmass⟩
      · exact Or.inr (Or.inl ⟨s, fun i j => by simpa [hconst] using hAB i j⟩)
      · refine Or.inr (Or.inr ⟨τ,hmass,?_⟩)
        intro i j
        by_cases hj : j = τ i
        · simp [hj]
        · rw [hAB, hperm]
          simp [hj]
  · rintro (⟨i,hzero⟩ | ⟨c,hconst⟩ | ⟨τ,hmass,hperm⟩)
    · rw [expectation_zero_row ν A i hzero]
      have hp : (∏ k : Row, ∑ j : Row, A k j ^ 2) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hzero]
      rw [hp]
      norm_num
    · have hE : expectation ν A = ∏ i : Row, c i := by
        unfold expectation
        simp only [hconst, ← Finset.sum_mul, hν.probability.mass, one_mul]
      rw [hE]
      have hi : ∀ i : Row, (∑ j : Row, A i j ^ 2) = 4 * c i ^ 2 := by
        intro i
        simp [hconst]
      simp only [hi, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      norm_num
    · have hfun : A = fun i j => if j = τ i then A i (τ i) else 0 :=
        funext fun i => funext (hperm i)
      have hE : expectation ν A = ν τ * ∏ i : Row, A i (τ i) := by
        conv_lhs => rw [hfun]
        exact expectation_permutation_rows ν τ (fun i => A i (τ i))
      have hi : ∀ i : Row, (∑ j : Row, A i j ^ 2) = A i (τ i)^2 := by
        intro i
        apply Finset.sum_eq_single (τ i)
        · intro j _ hj
          rw [hperm i j]
          simp [hj]
        · simp
      rw [hE, hmass]
      simp only [hi, Finset.prod_pow]
      ring

end
end FourRow
