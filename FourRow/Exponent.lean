module

public import FourRow.Stability
public import FourRow.Entropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Explicit exponents from stability and finite probability Lp norms. -/
namespace FourRow
noncomputable section
open Set

/-- Uniform mean on the four columns. -/
def meanFour (f : Vector) : ℝ := (∑ i : Fin 4, f i)/4

def varianceFour (f : Vector) : ℝ := meanFour (fun i => f i^2) - meanFour f ^ 2

def powerMoment (f : Vector) (p : ℝ) : ℝ := meanFour (fun i => f i ^ p)

def logPowerNorm (f : Vector) (p : ℝ) : ℝ := Real.log (powerMoment f p)/p

def powerNorm (f : Vector) (p : ℝ) : ℝ := powerMoment f p ^ (1/p)

/-- Independent-copy variance formula, written over the six unordered pairs. -/
theorem varianceFour_identity (f : Vector) :
    16*varianceFour f = (f 0-f 1)^2+(f 0-f 2)^2+(f 0-f 3)^2+
      (f 1-f 2)^2+(f 1-f 3)^2+(f 2-f 3)^2 := by
  simp only [varianceFour,meanFour,Fin.sum_univ_four]
  ring

theorem varianceFour_nonneg (f : Vector) : 0 ≤ varianceFour f := by
  have h := varianceFour_identity f
  nlinarith [sq_nonneg (f 0-f 1),sq_nonneg (f 0-f 2),sq_nonneg (f 0-f 3),
    sq_nonneg (f 1-f 2),sq_nonneg (f 1-f 3),sq_nonneg (f 2-f 3)]

/-- Variance contracts under a scalar Lipschitz bound. -/
theorem varianceFour_le_of_lipschitz (f g : Vector) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ i j, |g i-g j| ≤ L*|f i-f j|) :
    varianceFour g ≤ L^2*varianceFour f := by
  have hh (i j : Fin 4) : (g i-g j)^2 ≤ L^2*(f i-f j)^2 := by
    have hi := sq_le_sq₀ (abs_nonneg (g i-g j)) (mul_nonneg hL (abs_nonneg (f i-f j))) |>.mpr (h i j)
    simpa only [mul_pow,sq_abs] using hi
  have hf := varianceFour_identity f
  have hg := varianceFour_identity g
  have h01 := hh 0 1
  have h02 := hh 0 2
  have h03 := hh 0 3
  have h12 := hh 1 2
  have h13 := hh 1 3
  have h23 := hh 2 3
  nlinarith only [hf,hg,h01,h02,h03,h12,h13,h23]

/-- Power functions on the normalized row range have the expected Lipschitz constant. -/
theorem rpow_lipschitz_two (p : ℝ) (hp : 1 ≤ p) (x y : ℝ)
    (hx : x ∈ Icc (0:ℝ) 2) (hy : y ∈ Icc (0:ℝ) 2) :
    |x^p-y^p| ≤ (p*2^(p-1))*|x-y| := by
  have hd (z : ℝ) (_hz : z ∈ Icc (0:ℝ) 2) :
      HasDerivWithinAt (fun z : ℝ => z^p) (p*z^(p-1)) (Icc (0:ℝ) 2) z :=
    (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Icc (0:ℝ) 2) : ‖p*z^(p-1)‖ ≤ p*2^(p-1) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hz.1 _))]
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1 hz.2 (by linarith)) (by linarith)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

/-- Moment lower bound needed to control the logarithmic norm derivative. -/
theorem rpow_lower_two (x p : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) : 2^(p-2)*x^2 ≤ x^p := by
  by_cases hz : x = 0
  · simp [hz,Real.zero_rpow (by linarith : p ≠ 0)]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hpow := Real.rpow_le_rpow_of_nonpos hxp hx2 (by linarith : p-2 ≤ 0)
  have hm := mul_le_mul_of_nonneg_right hpow (sq_nonneg x)
  have hid : x^(p-2)*x^2 = x^p := by
    rw [← Real.rpow_two,← Real.rpow_add hxp]
    congr 1
    ring
  rwa [hid] at hm

theorem normalized_entry_le_two (f : Vector) (_hf : ∀ i, 0 ≤ f i)
    (hn : meanFour (fun i => f i^2) = 1) (i : Fin 4) : f i ≤ 2 := by
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => f j^2) (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)
  unfold meanFour at hn
  nlinarith only [hsingle,hn,_hf i]

theorem powerMoment_lower (f : Vector) (hf : ∀ i, 0 ≤ f i)
    (hn : meanFour (fun i => f i^2) = 1) (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    2^(p-2) ≤ powerMoment f p := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    rpow_lower_two (f i) p (hf i) (normalized_entry_le_two f hf hn i) hp hp2)
  rw [← Finset.mul_sum] at h
  unfold meanFour at hn
  unfold powerMoment meanFour
  have hsum : ∑ i : Fin 4, f i^2 = 4 := by linarith only [hn]
  rw [hsum] at h
  linarith only [h]

def meanEntropy (g : Vector) : ℝ :=
  meanFour (fun i => g i*Real.log (g i/meanFour g))

/-- Entropy is bounded above by variance divided by the mean. -/
theorem meanEntropy_le_variance (g : Vector) (hg : ∀ i, 0 ≤ g i)
    (hm : 0 < meanFour g) : meanEntropy g ≤ varianceFour g/meanFour g := by
  have hi (i : Fin 4) : g i*Real.log (g i/meanFour g) ≤ (g i)^2/meanFour g-g i := by
    by_cases hz : g i = 0
    · simp [hz]
    have hp : 0 < g i := lt_of_le_of_ne (hg i) (Ne.symm hz)
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hp hm)) (hg i)
    convert h using 1
    ring
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_sub_distrib,← Finset.sum_div] at h
  have hm0 : (∑ i, g i) ≠ 0 := by
    dsimp [meanFour] at hm
    linarith only [hm]
  calc
    meanEntropy g ≤ ((∑ i, g i^2)/meanFour g - ∑ i, g i)/4 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = varianceFour g/meanFour g := by
      dsimp [varianceFour,meanFour]
      field_simp

private theorem hasDerivAt_nonneg_const_rpow (a p : ℝ) (ha : 0 ≤ a) (hp : 0 < p) :
    HasDerivAt (fun t : ℝ => a^t) (a^p*Real.log a) p := by
  by_cases hz : a = 0
  · subst a
    simp only [Real.log_zero,mul_zero]
    apply (hasDerivAt_const p (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hp] with t ht
    simp [Real.zero_rpow (ne_of_gt ht)]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    simpa only [id_eq,mul_one,one_mul,mul_comm] using (hasDerivAt_id p).const_rpow hap

theorem powerMoment_hasDerivAt (f : Vector) (hf : ∀ i, 0 ≤ f i) (p : ℝ) (hp : 0 < p) :
    HasDerivAt (powerMoment f) (meanFour (fun i => f i^p*Real.log (f i))) p := by
  exact (HasDerivAt.fun_sum (fun i _ => hasDerivAt_nonneg_const_rpow (f i) p (hf i) hp)).div_const 4

theorem powerEntropy_identity (f : Vector) (hf : ∀ i, 0 ≤ f i) (p : ℝ)
    (hp : 0 < p) (hm : 0 < powerMoment f p) :
    meanEntropy (fun i => f i^p) =
      p*meanFour (fun i => f i^p*Real.log (f i)) -
        powerMoment f p*Real.log (powerMoment f p) := by
  have hi (i : Fin 4) : f i^p*Real.log (f i^p/powerMoment f p) =
      p*(f i^p*Real.log (f i)) - f i^p*Real.log (powerMoment f p) := by
    by_cases hz : f i = 0
    · simp [hz,Real.zero_rpow (ne_of_gt hp)]
    have hpos : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hz)
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hpos p)) (ne_of_gt hm),Real.log_rpow hpos]
    ring
  change (∑ i, f i^p*Real.log (f i^p/powerMoment f p))/4 = _
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
  dsimp [meanFour,powerMoment]
  ring

theorem logPowerNorm_hasDerivAt (f : Vector) (hf : ∀ i, 0 ≤ f i) (p : ℝ)
    (hp : 0 < p) (hm : 0 < powerMoment f p) :
    HasDerivAt (logPowerNorm f)
      (meanEntropy (fun i => f i^p)/(p^2*powerMoment f p)) p := by
  have hd := ((powerMoment_hasDerivAt f hf p hp).log (ne_of_gt hm)).div
    (hasDerivAt_id p) (ne_of_gt hp)
  convert hd using 1
  · rfl
  · rw [powerEntropy_identity f hf p hp hm]
    simp only [id_eq,mul_one]
    field_simp [ne_of_gt hp,ne_of_gt hm]

/-- Uniform derivative bound along the exponent interval. -/
theorem logPowerNorm_derivative_le (f : Vector) (hf : ∀ i, 0 ≤ f i)
    (hn : meanFour (fun i => f i^2) = 1) (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    meanEntropy (fun i => f i^p)/(p^2*powerMoment f p) ≤ 4*varianceFour f := by
  have hp0 : 0 < p := by linarith only [hp]
  have hb : 0 < (2:ℝ)^(p-2) := Real.rpow_pos_of_pos (by norm_num) _
  have hlower := powerMoment_lower f hf hn p hp hp2
  have hm : 0 < powerMoment f p := lt_of_lt_of_le hb hlower
  have hv := varianceFour_le_of_lipschitz f (fun i => f i^p) (p*2^(p-1))
    (mul_nonneg (le_of_lt hp0) (Real.rpow_nonneg (by norm_num) _))
    (fun i j => rpow_lipschitz_two p hp (f i) (f j)
      ⟨hf i,normalized_entry_le_two f hf hn i⟩ ⟨hf j,normalized_entry_le_two f hf hn j⟩)
  have he := meanEntropy_le_variance (fun i => f i^p)
    (fun i => Real.rpow_nonneg (hf i) p) hm
  have hpow : (2:ℝ)^(p-1) = 2*2^(p-2) := by
    rw [show p-1 = (p-2)+1 by ring,Real.rpow_add (by norm_num)]
    norm_num
    ring
  rw [hpow] at hv
  have hV := varianceFour_nonneg f
  have hsq : ((2:ℝ)^(p-2))^2 ≤ powerMoment f p^2 :=
    (sq_le_sq₀ (le_of_lt hb) (le_of_lt hm)).mpr hlower
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 4*p^2*varianceFour f by positivity)
  have he' := (le_div_iff₀ hm).mp he
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hp0) hm)).mpr
  have hstep : meanEntropy (fun i => f i^p)*powerMoment f p ≤
      (4*varianceFour f*(p^2*powerMoment f p))*powerMoment f p := by
    nlinarith only [hv,hmul,he']
  exact (mul_le_mul_iff_of_pos_right hm).mp hstep

/-- Integrating the derivative from p to two loses at most four times variance. -/
theorem logPowerNorm_lower (f : Vector) (hf : ∀ i, 0 ≤ f i)
    (hn : meanFour (fun i => f i^2) = 1) (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    -4*(2-p)*varianceFour f ≤ logPowerNorm f p := by
  have hd (t : ℝ) (ht : t ∈ Icc p 2) := logPowerNorm_hasDerivAt f hf t
    (by linarith only [hp,ht.1])
    (lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (t-2))
      (powerMoment_lower f hf hn t (le_trans hp ht.1) ht.2))
  have hcont : ContinuousOn (logPowerNorm f) (Icc p 2) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (logPowerNorm f) (interior (Icc p 2)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hder (t : ℝ) (ht : t ∈ interior (Icc p 2)) :
      deriv (logPowerNorm f) t ≤ 4*varianceFour f := by
    have hti := interior_subset ht
    rw [(hd t hti).deriv]
    exact logPowerNorm_derivative_le f hf hn t (le_trans hp hti.1) hti.2
  have h := (convex_Icc p 2).image_sub_le_mul_sub_of_deriv_le hcont hdiff hder
    p ⟨le_rfl,hp2⟩ 2 ⟨hp2,le_rfl⟩ hp2
  have htwo : logPowerNorm f 2 = 0 := by
    simp only [logPowerNorm,powerMoment,Real.rpow_two,hn,Real.log_one,zero_div]
  rw [htwo] at h
  linarith only [h]

theorem powerNorm_eq_exp (f : Vector) (p : ℝ) (hm : 0 < powerMoment f p) :
    powerNorm f p = Real.exp (logPowerNorm f p) := by
  rw [powerNorm,Real.rpow_def_of_pos hm]
  congr 1
  dsimp [logPowerNorm]
  ring

/-- Product estimate matching the sharp variance deficit. -/
theorem product_powerNorm_lower (A : Rows) (hA : NonnegativeRows A) (hn : NormalizedRows A)
    (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    1-4*(2-p)*varianceSum A ≤ ∏ i : Row, powerNorm (A i) p := by
  have hlog (i : Row) := logPowerNorm_lower (A i) (hA i) (hn i) p hp hp2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlog i)
  have hv (i : Row) : varianceFour (A i) = 1-((∑ j, A i j)/4)^2 := by
    dsimp [varianceFour,meanFour]
    rw [hn i]
  simp_rw [hv] at hsum
  rw [← Finset.mul_sum] at hsum
  change -4*(2-p)*varianceSum A ≤ ∑ i, logPowerNorm (A i) p at hsum
  have hnorm (i : Row) : powerNorm (A i) p = Real.exp (logPowerNorm (A i) p) :=
    powerNorm_eq_exp (A i) p (lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (p-2))
      (powerMoment_lower (A i) (hA i) (hn i) p hp hp2))
  simp_rw [hnorm]
  rw [← Real.exp_sum]
  have hexp := Real.add_one_le_exp (∑ i, logPowerNorm (A i) p)
  linarith only [hsum,hexp]

def explicitExponent (r : ℝ) : ℝ := 2-(1-24*r)/36

/-- Explicit interior exponent for normalized rows. -/
theorem explicitExponent_normalized (hEndpoint : EndpointBound)
    (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) (hn : NormalizedRows A) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) (explicitExponent r) := by
  have hp : 1 ≤ explicitExponent r := by dsimp [explicitExponent]; linarith only [hr]
  have hp2 : explicitExponent r ≤ 2 := by dsimp [explicitExponent]; linarith only [hrmax]
  have hs := stability_of_endpoint hEndpoint ν r hr hrmax hν A hA hn
  have hl := product_powerNorm_lower A hA hn (explicitExponent r) hp hp2
  dsimp [explicitExponent] at hl ⊢
  nlinarith only [hs,hl]

theorem powerMoment_nonneg (f : Vector) (hf : ∀ i, 0 ≤ f i) (p : ℝ) :
    0 ≤ powerMoment f p := by
  apply div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hf i) p)) (by norm_num)

theorem powerNorm_nonneg (f : Vector) (hf : ∀ i, 0 ≤ f i) (p : ℝ) : 0 ≤ powerNorm f p :=
  Real.rpow_nonneg (powerMoment_nonneg f hf p) _

/-- Homogeneity of the finite probability Lp norm. -/
theorem powerNorm_mul (f : Vector) (hf : ∀ i, 0 ≤ f i) (c p : ℝ)
    (hc : 0 ≤ c) (hp : p ≠ 0) :
    powerNorm (fun i => c*f i) p = c*powerNorm f p := by
  have hm : powerMoment (fun i => c*f i) p = c^p*powerMoment f p := by
    have hi (i : Fin 4) : (c*f i)^p = c^p*f i^p := Real.mul_rpow hc (hf i)
    simp only [powerMoment,meanFour,hi,← Finset.mul_sum]
    ring
  rw [powerNorm,hm,Real.mul_rpow (Real.rpow_nonneg hc p) (powerMoment_nonneg f hf p),← Real.rpow_mul hc]
  rw [mul_one_div_cancel hp,Real.rpow_one]
  rfl

/-- The p(r) inequality for arbitrary nonnegative rows, including zero rows. -/
theorem explicitExponent_bound (hEndpoint : EndpointBound)
    (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) (explicitExponent r) := by
  classical
  by_cases hz : ∃ i, ∀ j, A i j = 0
  · obtain ⟨i,hi⟩ := hz
    have he : expectation ν A = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      have hp : ∏ k : Row, A k (σ k) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (hi (σ i))
      simp [hp]
    rw [he]
    exact Finset.prod_nonneg (fun i _ => powerNorm_nonneg (A i) (hA i) _)
  · let s : Row → ℝ := fun i => Real.sqrt (meanFour (fun j => A i j^2))
    have hm (i : Row) : 0 < meanFour (fun j => A i j^2) := by
      obtain ⟨j,hj⟩ := not_forall.mp (show ¬∀ j, A i j = 0 from fun hi => hz ⟨i,hi⟩)
      have hl := Finset.single_le_sum (s := Finset.univ) (f := fun j => A i j^2)
        (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ j)
      have hp := sq_pos_of_ne_zero hj
      dsimp [meanFour]
      linarith only [hl,hp]
    have hs : ∀ i, 0 < s i := fun i => Real.sqrt_pos.mpr (hm i)
    have hsq : ∀ i, s i^2 = meanFour (fun j => A i j^2) :=
      fun i => Real.sq_sqrt (le_of_lt (hm i))
    let B : Rows := fun i j => A i j/s i
    have hB : NonnegativeRows B := fun i j => div_nonneg (hA i j) (le_of_lt (hs i))
    have hnB : NormalizedRows B := by
      intro i
      dsimp [B]
      simp only [div_pow,← Finset.sum_div]
      have hmean : ∑ j, A i j^2 = 4*s i^2 := by
        have h := hsq i
        dsimp [meanFour] at h
        linarith only [h]
      rw [hmean]
      field_simp [ne_of_gt (hs i)]
    have hscale (i j : Row) : A i j = s i*B i j := by
      dsimp [B]
      field_simp [ne_of_gt (hs i)]
    have he : expectation ν A = (∏ i, s i)*expectation ν B := by
      dsimp [expectation]
      simp_rw [hscale,Finset.prod_mul_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    have hp : explicitExponent r ≠ 0 := by
      dsimp [explicitExponent]
      linarith only [hr]
    have hn (i : Row) : powerNorm (A i) (explicitExponent r) =
        s i*powerNorm (B i) (explicitExponent r) := by
      have hfun : A i = fun j => s i*B i j := funext (hscale i)
      rw [hfun]
      exact powerNorm_mul (B i) (hB i) (s i) _ (le_of_lt (hs i)) hp
    rw [he]
    simp_rw [hn]
    rw [Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_left
      (explicitExponent_normalized hEndpoint ν r hr hrmax hν B hB hnB)
      (Finset.prod_nonneg (fun i _ => le_of_lt (hs i)))

end
end FourRow
