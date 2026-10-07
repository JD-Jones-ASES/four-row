import FourRow.Finite
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.Real.Sqrt

/-! Human-facing real laws, balanced marginals, and total variation balls. -/
namespace FourRow
noncomputable section

abbrev Law := Perm4 → ℝ
abbrev Rows := Matrix Row Row ℝ

def uniformLaw : Law := fun _ => 1/24

structure Probability (ν : Law) : Prop where
  nonneg : ∀ σ, 0 ≤ ν σ
  mass : ∑ σ, ν σ = 1

def Balanced (ν : Law) : Prop := ∀ i j : Row,
  ∑ σ : Perm4, (if σ i = j then ν σ else 0) = 1/4

def tvDistance (ν : Law) : ℝ := (∑ σ : Perm4, |ν σ - uniformLaw σ|) / 2

structure InBall (ν : Law) (r : ℝ) : Prop where
  probability : Probability ν
  balanced : Balanced ν
  distance : tvDistance ν ≤ r

def expectation (ν : Law) (A : Rows) : ℝ := ∑ σ : Perm4, ν σ * ∏ i : Row, A i (σ i)

def NonnegativeRows (A : Rows) : Prop := ∀ i j, 0 ≤ A i j

def NormalizedRows (A : Rows) : Prop := ∀ i, (∑ j : Row, A i j ^ 2) / 4 = 1

def varianceSum (A : Rows) : ℝ := ∑ i : Row, (1 - ((∑ j : Row, A i j) / 4)^2)

/-- The endpoint assertion, separately proved from exhaustive rational certificates. -/
def EndpointBound : Prop := ∀ (ν : Law), InBall ν (1/24) →
  ∀ (A : Rows), NonnegativeRows A → NormalizedRows A → expectation ν A ≤ 1

theorem uniform_probability : Probability uniformLaw := by
  constructor
  · intro σ; norm_num [uniformLaw]
  · norm_num [uniformLaw, Fintype.card_perm]

theorem uniform_balanced : Balanced uniformLaw := by
  intro i j
  have hcard : (Finset.univ.filter (fun σ : Perm4 => σ i = j)).card = 6 := by
    fin_cases i <;> fin_cases j <;> decide
  rw [← Finset.sum_filter]
  norm_num [uniformLaw,hcard]

theorem tvDistance_nonneg (ν : Law) : 0 ≤ tvDistance ν := by
  dsimp [tvDistance]
  positivity

@[simp] theorem uniform_distance : tvDistance uniformLaw = 0 := by simp [tvDistance]

theorem uniform_inBall {r : ℝ} (hr : 0 ≤ r) : InBall uniformLaw r :=
  ⟨uniform_probability, uniform_balanced, by simpa using hr⟩

theorem uniform_expectation (A : Rows) : expectation uniformLaw A = A.permanent/24 := by
  rw [← Matrix.permanent_transpose]
  simp only [expectation, uniformLaw, Matrix.permanent, Matrix.transpose_apply,
    ← Finset.mul_sum]
  ring

end
end FourRow
