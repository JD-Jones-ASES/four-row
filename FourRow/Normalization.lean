import FourRow.Endpoint

namespace FourRow
noncomputable section

/-- Every matrix with nonzero rows is a positive row scaling of a normalized
matrix. The product identity records the exact square-root-free scaling. -/
theorem exists_row_normalization (A : Rows) (hA : NonnegativeRows A)
    (hz : ∀ i : Row, rowSquareSum A i ≠ 0) :
    ∃ (s : Row → ℝ) (B : Rows),
      (∀ i, 0 < s i) ∧ NonnegativeRows B ∧ NormalizedRows B ∧
      (∀ i j, A i j = s i * B i j) ∧
      (∏ i : Row, ∑ j : Row, A i j ^ 2) = 256 * (∏ i : Row, s i)^2 := by
  have hs : ∀ i : Row, 0 < rowSquareSum A i :=
    fun i => lt_of_le_of_ne (rowSquareSum_nonneg A i) (Ne.symm (hz i))
  let q : Row → ℝ := fun i => Real.sqrt (rowSquareSum A i)
  have hq : ∀ i : Row, 0 < q i := fun i => Real.sqrt_pos.mpr (hs i)
  have hq2 : ∀ i : Row, (q i)^2 = rowSquareSum A i :=
    fun i => Real.sq_sqrt (hs i).le
  let s : Row → ℝ := fun i => q i / 2
  let B : Rows := fun i j => (2 / q i) * A i j
  have hBnonneg : NonnegativeRows B := by
    intro i j
    exact mul_nonneg (div_nonneg (by norm_num) (hq i).le) (hA i j)
  have hBnorm : NormalizedRows B := by
    intro i
    change (∑ j : Row, ((2 / q i) * A i j)^2) / 4 = 1
    simp only [mul_pow, ← Finset.mul_sum]
    change ((2 / q i)^2 * rowSquareSum A i) / 4 = 1
    rw [div_pow, hq2]
    field_simp [ne_of_gt (hs i)]
    ring
  refine ⟨s, B, (fun i => div_pos (hq i) (by norm_num)), hBnonneg, hBnorm, ?_, ?_⟩
  · intro i j
    dsimp [s, B]
    field_simp [ne_of_gt (hq i)]
  · have he : ∀ i : Row, (∑ j : Row, A i j ^ 2) = 4 * s i ^ 2 := by
      intro i
      change rowSquareSum A i = 4 * (q i / 2)^2
      rw [div_pow, hq2]
      ring
    simp only [he, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    norm_num

/-- Equality in the squared endpoint survives positive row normalization. -/
theorem normalized_expectation_eq_one
    (ν : Law) (hν : Probability ν) (A B : Rows) (hB : NonnegativeRows B)
    (s : Row → ℝ) (hs : ∀ i, 0 < s i)
    (hAB : ∀ i j, A i j = s i * B i j)
    (hprod : (∏ i : Row, ∑ j : Row, A i j ^ 2) = 256 * (∏ i : Row, s i)^2)
    (he : 256 * (expectation ν A)^2 = ∏ i : Row, ∑ j : Row, A i j ^ 2) :
    expectation ν B = 1 := by
  have hfun : A = fun i j => s i * B i j := funext fun i => funext (hAB i)
  have hscale : expectation ν A = (∏ i : Row, s i) * expectation ν B := by
    rw [hfun]
    exact expectation_scale_rows ν B s
  have hp : 0 < ∏ i : Row, s i := Finset.prod_pos fun i _ => hs i
  have hnonneg := expectation_nonneg ν hν B hB
  rw [hprod, hscale, mul_pow] at he
  have hsq : (expectation ν B)^2 = 1 := by
    have hcoef : 0 < 256 * (∏ i : Row, s i)^2 := by positivity
    nlinarith only [he, hcoef]
  nlinarith

end
end FourRow
