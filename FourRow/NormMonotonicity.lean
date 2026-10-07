module

public import FourRow.Exponent

@[expose] public section

/-! Monotonicity of finite probability Lp norms, and all exponents above p(r). -/
namespace FourRow
noncomputable section
open Set

theorem meanEntropy_nonneg (g : Vector) (hg : ∀ i, 0 ≤ g i) (hm : 0 < meanFour g) :
    0 ≤ meanEntropy g := by
  let w : Vector := fun i => g i/(4*meanFour g)
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (hg i) (by positivity)
  have hmass : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    have he : ∑ i, g i = 4*meanFour g := by dsimp [meanFour]; ring
    rw [he]
    exact div_self (ne_of_gt (by positivity))
  have hk := finiteKL_nonneg_subprob w (fun _ => (1/4:ℝ)) hw (by intro i; norm_num)
    hmass (by norm_num) (by intro i hi; norm_num)
  have he : meanEntropy g = meanFour g*finiteKL w (fun _ => (1/4:ℝ)) := by
    dsimp [meanEntropy,meanFour] at ⊢
    unfold finiteKL
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change g i*Real.log (g i/meanFour g)/4 =
      meanFour g*(w i*Real.log (w i/(1/4:ℝ)))
    have hr : w i/(1/4:ℝ) = g i/meanFour g := by dsimp [w]; ring
    rw [hr]
    dsimp [w]
    field_simp
  rw [he]
  exact mul_nonneg (le_of_lt hm) hk

theorem powerMoment_pos_of_nonzero (f : Vector) (hf : ∀ i, 0 ≤ f i)
    (hn : ∃ i, f i ≠ 0) (p : ℝ) : 0 < powerMoment f p := by
  obtain ⟨i,hi⟩ := hn
  have hp := Real.rpow_pos_of_pos (lt_of_le_of_ne (hf i) (Ne.symm hi)) p
  have hl := Finset.single_le_sum (s := Finset.univ) (f := fun j => f j^p)
    (fun j _ => Real.rpow_nonneg (hf j) p) (Finset.mem_univ i)
  dsimp [powerMoment,meanFour]
  linarith only [hp,hl]

theorem powerNorm_mono (f : Vector) (hf : ∀ i, 0 ≤ f i) (p q : ℝ)
    (hp : 0 < p) (hpq : p ≤ q) : powerNorm f p ≤ powerNorm f q := by
  classical
  by_cases hn : ∃ i, f i ≠ 0
  · have hd (t : ℝ) (ht : t ∈ Icc p q) := logPowerNorm_hasDerivAt f hf t
      (lt_of_lt_of_le hp ht.1) (powerMoment_pos_of_nonzero f hf hn t)
    have hcont : ContinuousOn (logPowerNorm f) (Icc p q) :=
      fun t ht => (hd t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (logPowerNorm f) (interior (Icc p q)) :=
      fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    have hder (t : ℝ) (ht : t ∈ interior (Icc p q)) : 0 ≤ deriv (logPowerNorm f) t := by
      rw [(hd t (interior_subset ht)).deriv]
      apply div_nonneg
      · exact meanEntropy_nonneg (fun i => f i^t) (fun i => Real.rpow_nonneg (hf i) t)
          (powerMoment_pos_of_nonzero f hf hn t)
      · exact mul_nonneg (sq_nonneg t) (le_of_lt (powerMoment_pos_of_nonzero f hf hn t))
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont hdiff hder
    rw [powerNorm_eq_exp f p (powerMoment_pos_of_nonzero f hf hn p),
      powerNorm_eq_exp f q (powerMoment_pos_of_nonzero f hf hn q)]
    exact Real.exp_le_exp.mpr (hmono ⟨le_rfl,hpq⟩ ⟨hpq,le_rfl⟩ hpq)
  · have hz : ∀ i, f i = 0 := by simpa only [not_exists,not_not] using hn
    have hq : 0 < q := lt_of_lt_of_le hp hpq
    simp [powerNorm,powerMoment,meanFour,hz,Real.zero_rpow (ne_of_gt hp),
      Real.zero_rpow (ne_of_gt hq),Real.zero_rpow (inv_ne_zero (ne_of_gt hp)),
      Real.zero_rpow (inv_ne_zero (ne_of_gt hq))]

theorem explicitExponent_range (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24) :
    71/36 ≤ explicitExponent r ∧ explicitExponent r ≤ 2 := by
  dsimp [explicitExponent]
  constructor <;> linarith only [hr,hrmax]

theorem explicitExponent_lt_two (r : ℝ) : explicitExponent r < 2 ↔ r < 1/24 := by
  dsimp [explicitExponent]
  constructor <;> intro h <;> linarith only [h]

/-- Every larger positive exponent also satisfies the row-product bound. -/
theorem largerExponent_bound (hEndpoint : EndpointBound)
    (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24) (hν : InBall ν r)
    (A : Rows) (hA : NonnegativeRows A) (p : ℝ) (hp : explicitExponent r ≤ p) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) p := by
  apply le_trans (explicitExponent_bound hEndpoint ν r hr hrmax hν A hA)
  apply Finset.prod_le_prod₀
  · intro i _
    exact powerNorm_nonneg (A i) (hA i) _
  · intro i _
    apply powerNorm_mono (A i) (hA i) _ p ?_ hp
    have h := (explicitExponent_range r hr hrmax).1
    linarith only [h]

end
end FourRow
