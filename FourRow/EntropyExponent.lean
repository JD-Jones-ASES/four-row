import FourRow.Exponent

/-! Generic finite Lp/entropy duality and its explicit-radius specialization. -/
namespace FourRow
noncomputable section

def powerEntropyRows (ρ : Law) (p : ℝ) : Rows :=
  fun i j => (4*marginal ρ i j)^(1/p)

theorem powerEntropyRows_nonneg (ρ : Law) (hρ : Probability ρ) (p : ℝ) :
    NonnegativeRows (powerEntropyRows ρ p) := fun i j =>
  Real.rpow_nonneg (mul_nonneg (by norm_num) (marginal_nonneg ρ hρ i j)) _

theorem powerEntropyRows_norm (ρ : Law) (hρ : Probability ρ) (p : ℝ) (hp : 0 < p)
    (i : Row) : powerNorm (powerEntropyRows ρ p i) p = 1 := by
  have hi (j : Row) : (powerEntropyRows ρ p i j)^p = 4*marginal ρ i j := by
    rw [powerEntropyRows,← Real.rpow_mul (mul_nonneg (by norm_num) (marginal_nonneg ρ hρ i j))]
    rw [one_div_mul_cancel (ne_of_gt hp),Real.rpow_one]
  simp only [powerNorm,powerMoment,meanFour,hi,← Finset.mul_sum,marginal_mass ρ hρ i]
  norm_num

private theorem powerEntropyRows_positive (ρ : Law) (hρ : Probability ρ)
    (p : ℝ) (σ : Perm4) (hs : 0 < ρ σ) (i : Row) :
    0 < powerEntropyRows ρ p i (σ i) := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (by norm_num) (lt_of_lt_of_le hs (atom_le_marginal ρ hρ σ i))

/-- Finite entropy duality for any finite probability-Lp product inequality. -/
theorem entropy_of_powerBound_supported (ν ρ : Law) (hν : Probability ν)
    (hρ : Probability ρ) (p : ℝ) (hp : 0 < p) (hs : Supports ρ ν)
    (hbound : ∀ A : Rows, NonnegativeRows A → expectation ν A ≤ ∏ i, powerNorm (A i) p) :
    marginalEntropySum ρ ≤ p*finiteKL ρ ν := by
  let g : Perm4 → ℝ := fun σ => ∏ i : Row, powerEntropyRows ρ p i (σ i)
  let q : Law := fun σ => ν σ*g σ
  have hg : ∀ σ, 0 ≤ g σ := by
    intro σ
    exact Finset.prod_nonneg (fun i _ => powerEntropyRows_nonneg ρ hρ p i (σ i))
  have hgp : ∀ σ, 0 < ρ σ → 0 < g σ := by
    intro σ hpos
    exact Finset.prod_pos (fun i _ => powerEntropyRows_positive ρ hρ p σ hpos i)
  have hq : ∀ σ, 0 ≤ q σ := fun σ => mul_nonneg (hν.nonneg σ) (hg σ)
  have hqs : Supports ρ q := fun σ hpos => mul_pos (hs σ hpos) (hgp σ hpos)
  have hqm : ∑ σ, q σ ≤ 1 := by
    change expectation ν (powerEntropyRows ρ p) ≤ 1
    have h := hbound (powerEntropyRows ρ p) (powerEntropyRows_nonneg ρ hρ p)
    simpa only [powerEntropyRows_norm ρ hρ p hp,Finset.prod_const_one] using h
  have hkl := finiteKL_nonneg_subprob ρ q hρ.nonneg hq hρ.mass hqm hqs
  have hlogs (σ : Perm4) : ρ σ*Real.log (ρ σ/q σ) =
      ρ σ*Real.log (ρ σ/ν σ) - (ρ σ/p)*∑ i : Row, Real.log (4*marginal ρ i (σ i)) := by
    by_cases hz : ρ σ = 0
    · simp [hz]
    have hpos : 0 < ρ σ := lt_of_le_of_ne (hρ.nonneg σ) (Ne.symm hz)
    have hνp := hs σ hpos
    have hprod := hgp σ hpos
    have hlogg : Real.log (g σ) = (∑ i : Row, Real.log (4*marginal ρ i (σ i)))/p := by
      dsimp [g]
      rw [Real.log_prod (fun i _ => ne_of_gt (powerEntropyRows_positive ρ hρ p σ hpos i))]
      have hl (i : Row) : Real.log (powerEntropyRows ρ p i (σ i)) =
          Real.log (4*marginal ρ i (σ i))/p := by
        rw [powerEntropyRows,Real.log_rpow
          (mul_pos (by norm_num) (lt_of_lt_of_le hpos (atom_le_marginal ρ hρ σ i)))]
        ring
      simp_rw [hl,← Finset.sum_div]
    dsimp [q]
    rw [Real.log_div hz (ne_of_gt (mul_pos hνp hprod)),
      Real.log_mul (ne_of_gt hνp) (ne_of_gt hprod),Real.log_div hz (ne_of_gt hνp),hlogg]
    ring
  have hdouble : ∑ σ : Perm4, (ρ σ/p)*∑ i : Row, Real.log (4*marginal ρ i (σ i)) =
      marginalEntropySum ρ/p := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold marginalEntropySum finiteKL
    simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [marginal_sum ρ i (fun j => Real.log (4*marginal ρ i j))]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ring
  unfold finiteKL at hkl
  simp_rw [hlogs] at hkl
  rw [Finset.sum_sub_distrib,hdouble] at hkl
  change 0 ≤ finiteKL ρ ν-marginalEntropySum ρ/p at hkl
  have h : marginalEntropySum ρ/p ≤ finiteKL ρ ν := by linarith only [hkl]
  have := (div_le_iff₀ hp).mp h
  linarith only [this]

theorem entropy_of_powerBound (ν ρ : Law) (hν : Probability ν) (hρ : Probability ρ)
    (p : ℝ) (hp : 0 < p)
    (hbound : ∀ A : Rows, NonnegativeRows A → expectation ν A ≤ ∏ i, powerNorm (A i) p) :
    (marginalEntropySum ρ : EReal) ≤ (p:EReal)*relativeEntropy ρ ν := by
  classical
  by_cases hs : Supports ρ ν
  · rw [relativeEntropy,ite_eq_left hs,← EReal.coe_mul]
    exact EReal.coe_le_coe (entropy_of_powerBound_supported ν ρ hν hρ p hp hs hbound)
  · rw [relativeEntropy,ite_eq_right hs,EReal.coe_mul_top_of_pos hp]
    exact le_top

/-- Entropy bound with the explicit strict-interior coefficient p(r). -/
theorem explicitExponent_entropy (hEndpoint : EndpointBound)
    (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (marginalEntropySum ρ : EReal) ≤ (explicitExponent r : EReal)*relativeEntropy ρ ν := by
  have hp : 0 < explicitExponent r := by dsimp [explicitExponent]; linarith only [hr]
  exact entropy_of_powerBound ν ρ hν.probability hρ _ hp
    (fun A hA => explicitExponent_bound hEndpoint ν r hr hrmax hν A hA)

/-- Coordinate observation contracts relative entropy by p(r)/4. -/
theorem explicitExponent_observation_entropy (hEndpoint : EndpointBound)
    (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (finiteKL (observationLaw ρ) (observationLaw ν) : EReal) ≤
      ((explicitExponent r/4:ℝ):EReal)*relativeEntropy ρ ν := by
  classical
  have hp : 0 < explicitExponent r := by dsimp [explicitExponent]; linarith only [hr]
  rw [observationLaw_of_balanced ν hν.balanced,observation_entropy_identity]
  by_cases hs : Supports ρ ν
  · rw [relativeEntropy,ite_eq_left hs,← EReal.coe_mul]
    apply EReal.coe_le_coe
    have h := entropy_of_powerBound_supported ν ρ hν.probability hρ _ hp hs
      (fun A hA => explicitExponent_bound hEndpoint ν r hr hrmax hν A hA)
    linarith only [h]
  · rw [relativeEntropy,ite_eq_right hs,EReal.coe_mul_top_of_pos (div_pos hp (by norm_num))]
    exact le_top

end
end FourRow
