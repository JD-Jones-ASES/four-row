import FourRow.Endpoint

namespace FourRow
noncomputable section

/-- Cross-multiplied orbit identities imply exact normalization over the reals. -/
theorem normalized_moved_of_crossmul (x y : PermIndex → ℝ) (g : Relabel) (t : ℝ)
    (hm : Circuit.mass x ≠ 0)
    (hxy : ∀ p : PermIndex, t * x (action g p) = Circuit.mass x * y p) :
    (t / Circuit.mass x) • x = movedVector g y := by
  ext p
  have h := hxy ((action g).symm p)
  simp only [Equiv.apply_symm_apply] at h
  change t / Circuit.mass x * x p = y ((action g).symm p)
  apply (mul_right_cancel₀ hm)
  calc
    _ = t * x p := by field_simp
    _ = _ := by simpa [mul_comm] using h

theorem weightedPolynomial_moved (g : Relabel) (x : PermIndex → ℝ) (A : Rows) :
    weightedPolynomial (movedVector g x) A = weightedPolynomial x (relabelRows g A) := by
  simpa [weightedPolynomial, movedVector] using weighted_monomial_moved g (fun p => 1 + x p) A

theorem quarticTarget_relabel (g : Relabel) (A : Rows) :
    quarticTarget (relabelRows g A) = quarticTarget A := by
  simp only [quarticTarget, sum_squares_relabel]

end
end FourRow
