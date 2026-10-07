module

public import FourRow.Entropy
public import FourRow.Sharpness

@[expose] public section

namespace FourRow
noncomputable section

/-- Point mass at the identity permutation. -/
def identityLaw : Law := fun σ => if σ = 1 then 1 else 0

theorem identityLaw_probability : Probability identityLaw := by
  classical
  constructor
  · intro σ; simp only [identityLaw]; split_ifs <;> norm_num
  · simp [identityLaw]

theorem lex_zero : lexEquiv (0 : PermIndex) = 1 := by
  ext i
  fin_cases i <;> rfl

theorem lex_symm_one : lexEquiv.symm 1 = (0 : PermIndex) := by
  rw [← lex_zero, Equiv.symm_apply_apply]

theorem identityLaw_supports : Supports identityLaw (sharpLaw (1/24)) := by
  intro σ h
  by_cases hs : σ = 1
  · subst σ; norm_num [sharpLaw, lex_symm_one, sharpTrade]
  · simp [identityLaw,hs] at h

theorem identityLaw_marginal (i j : Row) : marginal identityLaw i j = if j = i then 1 else 0 := by
  classical
  unfold marginal
  rw [Finset.sum_eq_single 1]
  · simp [identityLaw, eq_comm]
  · intro σ _ hs; simp [identityLaw,hs]
  · simp

theorem identityLaw_KL : finiteKL identityLaw (sharpLaw (1/24)) = Real.log 16 := by
  classical
  unfold finiteKL
  rw [Finset.sum_eq_single 1]
  · norm_num [identityLaw, sharpLaw, lex_symm_one, sharpTrade]
  · intro σ _ hs; simp [identityLaw,hs]
  · simp

theorem identityLaw_marginalEntropy : marginalEntropySum identityLaw = 4*Real.log 4 := by
  classical
  simp [marginalEntropySum, finiteKL, identityLaw_marginal, eq_comm]

theorem log_sixteen : Real.log 16 = 2*Real.log 4 := by
  have h := Real.log_pow (4:ℝ) 2
  norm_num at h
  exact h

/-- The endpoint entropy coefficient2 is optimal on the entire balanced ball. -/
theorem entropy_coefficient_ge_two (κ : ℝ)
    (h : ∀ ν, InBall ν (1/24) → ∀ ρ, Probability ρ → Supports ρ ν →
      marginalEntropySum ρ ≤ κ*finiteKL ρ ν) : 2 ≤ κ := by
  have hb := sharpLaw_inBall (1/24) (by norm_num) (by norm_num)
  have hs := h _ hb identityLaw identityLaw_probability identityLaw_supports
  rw [identityLaw_marginalEntropy,identityLaw_KL,log_sixteen] at hs
  have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
  nlinarith

end
end FourRow
