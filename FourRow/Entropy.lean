import FourRow.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Operations

/-! Finite entropy duality. The real-valued formula is used only when the
reference law supports the first law; the extended version assigns infinity
otherwise. No full-support assumption is made on the balanced reference law. -/
namespace FourRow
noncomputable section

/-- Support condition appropriate for nonnegative finite weights. -/
def Supports {α : Type*} (p q : α → ℝ) : Prop := ∀ a, 0 < p a → 0 < q a

/-- Finite relative entropy, with `0 * log 0 = 0`. Use with `Supports`. -/
def finiteKL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- Relative entropy including unsupported laws, with value positive infinity. -/
def relativeEntropy {α : Type*} [Fintype α] (p q : α → ℝ) : EReal :=
  by classical exact if Supports p q then (finiteKL p q : EReal) else ⊤

private theorem mul_log_ratio_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) : x-y ≤ x*Real.log (x/y) := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; simpa using hy
  · have hpy := hs hp
    have hlog := Real.log_le_sub_one_of_pos (div_pos hpy hp)
    rw [Real.log_div (ne_of_gt hpy) (ne_of_gt hp)] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog hx
    have hc : x * (y/x-1) = y-x := by field_simp
    rw [hc] at hm
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hpy)]
    nlinarith only [hm]

/-- Gibbs inequality for a probability weight and a subprobability reference. -/
theorem finiteKL_nonneg_subprob {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hmass : ∑ a, p a = 1) (hqmass : ∑ a, q a ≤ 1) (hs : Supports p q) :
    0 ≤ finiteKL p q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    mul_log_ratio_ge (p a) (q a) (hp a) (hq a) (hs a))
  rw [Finset.sum_sub_distrib,hmass] at h
  unfold finiteKL
  linarith only [h,hqmass]

/-- Coordinate marginal of a permutation law. -/
def marginal (ρ : Law) (i j : Row) : ℝ := ∑ σ : Perm4,
  if σ i = j then ρ σ else 0

theorem marginal_nonneg (ρ : Law) (hρ : Probability ρ) (i j : Row) :
    0 ≤ marginal ρ i j := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs <;> first | exact hρ.nonneg σ | rfl

theorem marginal_mass (ρ : Law) (hρ : Probability ρ) (i : Row) :
    ∑ j : Row, marginal ρ i j = 1 := by
  unfold marginal
  rw [Finset.sum_comm]
  simpa using hρ.mass

theorem atom_le_marginal (ρ : Law) (hρ : Probability ρ) (σ : Perm4) (i : Row) :
    ρ σ ≤ marginal ρ i (σ i) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun τ : Perm4 => if τ i = σ i then ρ τ else 0)
    (fun τ _ => by split_ifs <;> first | exact hρ.nonneg τ | rfl) (Finset.mem_univ σ)
  simpa [marginal] using h

/-- Finite pushforward integration formula, including zero marginal cells. -/
theorem marginal_sum (ρ : Law) (i : Row) (f : Row → ℝ) :
    ∑ σ : Perm4, ρ σ * f (σ i) = ∑ j : Row, marginal ρ i j * f j := by
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp

/-- The probability-L²-normalized functions used in endpoint entropy duality. -/
def entropyRows (ρ : Law) : Rows := fun i j => Real.sqrt (4*marginal ρ i j)

theorem entropyRows_nonneg (ρ : Law) : NonnegativeRows (entropyRows ρ) :=
  fun _ _ => Real.sqrt_nonneg _

theorem entropyRows_normalized (ρ : Law) (hρ : Probability ρ) :
    NormalizedRows (entropyRows ρ) := by
  intro i
  have hs (j : Row) : entropyRows ρ i j ^ 2 = 4*marginal ρ i j :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (marginal_nonneg ρ hρ i j))
  simp_rw [hs]
  rw [← Finset.mul_sum,marginal_mass ρ hρ i]
  norm_num

private theorem entropyRows_positive (ρ : Law) (hρ : Probability ρ)
    (σ : Perm4) (hs : 0 < ρ σ) (i : Row) : 0 < entropyRows ρ i (σ i) := by
  apply Real.sqrt_pos.mpr
  have hm := atom_le_marginal ρ hρ σ i
  exact mul_pos (by norm_num) (lt_of_lt_of_le hs hm)

/-- KL of each marginal against uniform measure on four points. -/
def marginalEntropySum (ρ : Law) : ℝ :=
  ∑ i : Row, finiteKL (marginal ρ i) (fun _ => 1/4)

theorem marginalEntropySum_nonneg (ρ : Law) (hρ : Probability ρ) :
    0 ≤ marginalEntropySum ρ := by
  apply Finset.sum_nonneg
  intro i _
  apply finiteKL_nonneg_subprob _ _ (marginal_nonneg ρ hρ i) (by intro j; norm_num)
    (marginal_mass ρ hρ i) (by norm_num)
  intro j hj
  norm_num

/-- The entropy comparison induced by the endpoint four-row inequality. -/
theorem endpoint_entropy_supported (hEndpoint : EndpointBound)
    (ν ρ : Law) (hν : InBall ν (1/24)) (hρ : Probability ρ) (hs : Supports ρ ν) :
    marginalEntropySum ρ ≤ 2*finiteKL ρ ν := by
  let g : Perm4 → ℝ := fun σ => ∏ i : Row, entropyRows ρ i (σ i)
  let q : Law := fun σ => ν σ * g σ
  have hg : ∀ σ, 0 ≤ g σ := by
    intro σ
    apply Finset.prod_nonneg
    intro i _
    exact entropyRows_nonneg ρ i (σ i)
  have hgp : ∀ σ, 0 < ρ σ → 0 < g σ := by
    intro σ hp
    apply Finset.prod_pos
    intro i _
    exact entropyRows_positive ρ hρ σ hp i
  have hq : ∀ σ, 0 ≤ q σ := fun σ => mul_nonneg (hν.probability.nonneg σ) (hg σ)
  have hqs : Supports ρ q := fun σ hp => mul_pos (hs σ hp) (hgp σ hp)
  have hqm : ∑ σ, q σ ≤ 1 := hEndpoint ν hν (entropyRows ρ)
    (entropyRows_nonneg ρ) (entropyRows_normalized ρ hρ)
  have hkl := finiteKL_nonneg_subprob ρ q hρ.nonneg hq hρ.mass hqm hqs
  have hlogs (σ : Perm4) : ρ σ * Real.log (ρ σ / q σ) =
      ρ σ * Real.log (ρ σ / ν σ) -
        (ρ σ/2) * ∑ i : Row, Real.log (4*marginal ρ i (σ i)) := by
    by_cases hz : ρ σ = 0
    · simp [hz]
    have hp : 0 < ρ σ := lt_of_le_of_ne (hρ.nonneg σ) (Ne.symm hz)
    have hνp := hs σ hp
    have hprod := hgp σ hp
    have hlogg : Real.log (g σ) = (∑ i : Row, Real.log (4*marginal ρ i (σ i)))/2 := by
      dsimp [g]
      rw [Real.log_prod (fun i _ => ne_of_gt (entropyRows_positive ρ hρ σ hp i))]
      have hl (i : Row) : Real.log (entropyRows ρ i (σ i)) =
          Real.log (4*marginal ρ i (σ i))/2 :=
        Real.log_sqrt (mul_nonneg (by norm_num) (marginal_nonneg ρ hρ i (σ i)))
      simp_rw [hl,← Finset.sum_div]
    dsimp [q]
    rw [Real.log_div hz (ne_of_gt (mul_pos hνp hprod)),
      Real.log_mul (ne_of_gt hνp) (ne_of_gt hprod),Real.log_div hz (ne_of_gt hνp),hlogg]
    ring
  have hdouble : ∑ σ : Perm4, (ρ σ/2) * ∑ i : Row, Real.log (4*marginal ρ i (σ i)) =
      marginalEntropySum ρ/2 := by
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
  change 0 ≤ finiteKL ρ ν - marginalEntropySum ρ/2 at hkl
  linarith only [hkl]

/-- All laws, including those with infinite relative entropy. -/
theorem endpoint_entropy (hEndpoint : EndpointBound)
    (ν ρ : Law) (hν : InBall ν (1/24)) (hρ : Probability ρ) :
    (marginalEntropySum ρ : EReal) ≤ ((2:ℝ):EReal)*relativeEntropy ρ ν := by
  classical
  by_cases hs : Supports ρ ν
  · rw [relativeEntropy,ite_eq_left hs]
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe (endpoint_entropy_supported hEndpoint ν ρ hν hρ hs)
  · rw [relativeEntropy,ite_eq_right hs,EReal.coe_mul_top_of_pos (by norm_num)]
    exact le_top

/-- Observe a uniformly chosen row label together with its image. -/
def observationLaw (ρ : Law) : Row × Row → ℝ :=
  fun ij => marginal ρ ij.1 ij.2 / 4

def observationUniform : Row × Row → ℝ := fun _ => 1/16

/-- Balance makes the observed reference law exactly uniform on sixteen cells. -/
theorem observationLaw_of_balanced (ν : Law) (hν : Balanced ν) :
    observationLaw ν = observationUniform := by
  funext ij
  dsimp [observationLaw,observationUniform,marginal]
  rw [hν ij.1 ij.2]
  norm_num

/-- The factor one fourth is an exact entropy identity. -/
theorem observation_entropy_identity (ρ : Law) :
    finiteKL (observationLaw ρ) observationUniform = marginalEntropySum ρ/4 := by
  simp only [finiteKL, observationLaw, observationUniform, marginalEntropySum]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (marginal ρ i j/4)/(1/16:ℝ) = marginal ρ i j/(1/4:ℝ) := by ring
  rw [he]
  ring

/-- Sharp endpoint observation contraction, valid also for infinite input KL. -/
theorem endpoint_observation_entropy (hEndpoint : EndpointBound)
    (ν ρ : Law) (hν : InBall ν (1/24)) (hρ : Probability ρ) :
    (finiteKL (observationLaw ρ) (observationLaw ν) : EReal) ≤
      ((1/2:ℝ) : EReal)*relativeEntropy ρ ν := by
  classical
  rw [observationLaw_of_balanced ν hν.balanced,observation_entropy_identity]
  by_cases hs : Supports ρ ν
  · rw [relativeEntropy,ite_eq_left hs,← EReal.coe_mul]
    apply EReal.coe_le_coe
    have h := endpoint_entropy_supported hEndpoint ν ρ hν hρ hs
    linarith only [h]
  · rw [relativeEntropy,ite_eq_right hs,EReal.coe_mul_top_of_pos (by norm_num)]
    exact le_top

end
end FourRow
