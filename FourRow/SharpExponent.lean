import FourRow.Exponent
import FourRow.Sharpness

namespace FourRow
noncomputable section

/-- Matching singleton rows have norm strictly less than one below exponent two. -/
theorem sharpRows_powerNorm_lt_one (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) (i : Row) :
    powerNorm (sharpRows i) p < 1 := by
  have hp0 : 0 < p := by linarith
  have hm : powerMoment (sharpRows i) p = (2:ℝ)^p/4 := by
    fin_cases i <;>
      simp [powerMoment, meanFour, sharpRows, Real.zero_rpow (ne_of_gt hp0)]
  have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hp2
  rw [Real.rpow_two] at h2
  apply Real.rpow_lt_one (powerMoment_nonneg _ (sharpRows_nonnegative i) p)
  · rw [hm]; linarith
  · exact one_div_pos.mpr hp0

/-- The endpoint law obstructs every common exponent below two. -/
theorem no_subcritical_at_endpoint (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) :
    (∏ i : Row, powerNorm (sharpRows i) p) < expectation (sharpLaw (1/24)) sharpRows := by
  rw [sharpLaw_expectation]
  norm_num
  have hn := fun i => powerNorm_nonneg (sharpRows i) (sharpRows_nonnegative i) p
  have hl := sharpRows_powerNorm_lt_one p hp hp2
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  norm_num
  have h01 := mul_lt_mul_of_nonneg (hl 0) (hl 1) (hn 0) (hn 1)
  have h23 := mul_lt_mul_of_nonneg (hl 2) (hl 3) (hn 2) (hn 3)
  have hprod := mul_lt_mul_of_nonneg h01 h23
    (mul_nonneg (hn 0) (hn 1)) (mul_nonneg (hn 2) (hn 3))
  simpa [mul_assoc] using hprod

/-- Exact feasibility threshold for a uniform exponent strictly below two. -/
theorem subcritical_exponent_iff (hEndpoint : EndpointBound) (r : ℝ) (hr : 0 ≤ r) :
    (∃ p : ℝ, 1 ≤ p ∧ p < 2 ∧ ∀ ν, InBall ν r → ∀ A, NonnegativeRows A →
      expectation ν A ≤ ∏ i : Row, powerNorm (A i) p) ↔ r < 1/24 := by
  constructor
  · rintro ⟨p,hp,hp2,hbound⟩
    by_contra h
    have hr' : 1/24 ≤ r := le_of_not_gt h
    have hs := sharpLaw_inBall (1/24) (by norm_num) (by norm_num)
    have hb : InBall (sharpLaw (1/24)) r :=
      ⟨hs.probability, hs.balanced, hs.distance.trans hr'⟩
    have hu := hbound _ hb sharpRows sharpRows_nonnegative
    exact (not_lt_of_ge hu) (no_subcritical_at_endpoint p hp hp2)
  · intro h
    refine ⟨explicitExponent r, ?_, ?_, ?_⟩
    · unfold explicitExponent; linarith
    · unfold explicitExponent; linarith
    · intro ν hν A hA
      exact explicitExponent_bound hEndpoint ν r hr (le_of_lt h) hν A hA

end
end FourRow
