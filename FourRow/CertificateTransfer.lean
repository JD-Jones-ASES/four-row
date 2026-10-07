import FourRow.Orientations
import FourRow.CensusTables
import FourRow.OrbitTransfer

namespace FourRow
noncomputable section

/-- Real realization of a literal integer census primitive. -/
def primitiveReal (k : Fin 73) : PermIndex → ℝ := fun p => (Census.primitive k p : ℝ)

def representativeReal (k : Fin 131) : PermIndex → ℝ := fun p => (representative k p : ℝ)

theorem primitiveReal_mass (k : Fin 73) :
    Circuit.mass (primitiveReal k) = (Census.primitiveL1 k : ℝ) := by
  unfold Circuit.mass primitiveReal
  exact_mod_cast Census.primitiveL1_eq k

theorem primitiveReal_mass_pos (k : Fin 73) : 0 < Circuit.mass (primitiveReal k) := by
  rw [primitiveReal_mass]
  exact_mod_cast Census.primitiveL1_pos k

theorem primitive_normalized_positive (k : Fin 73) :
    (2 / Circuit.mass (primitiveReal k)) • primitiveReal k =
      movedVector (Census.relabel (Census.positiveRelabel k))
        (representativeReal (Census.positiveGram k)) := by
  apply normalized_moved_of_crossmul _ _ _ _ (ne_of_gt (primitiveReal_mass_pos k))
  intro p
  rw [primitiveReal_mass]
  have h := Census.positive_orientation_rat k p
  rw [Census.literalAction_eq] at h
  exact_mod_cast h

theorem primitive_normalized_negative (k : Fin 73) :
    -((2 / Circuit.mass (primitiveReal k)) • primitiveReal k) =
      movedVector (Census.relabel (Census.negativeRelabel k))
        (representativeReal (Census.negativeGram k)) := by
  have hxy : ∀ p : PermIndex,
      (-2 : ℝ) * primitiveReal k (action (Census.relabel (Census.negativeRelabel k)) p) =
        Circuit.mass (primitiveReal k) * representativeReal (Census.negativeGram k) p := by
    intro p
    rw [primitiveReal_mass]
    have h := Census.negative_orientation_rat k p
    rw [Census.literalAction_eq] at h
    exact_mod_cast h
  simpa only [neg_div, neg_smul] using normalized_moved_of_crossmul _ _ _ _
    (ne_of_gt (primitiveReal_mass_pos k)) hxy

theorem weightedPolynomial_representative (k : Fin 131) (A : Rows) :
    weightedPolynomial (representativeReal k) A =
      ∑ p : PermIndex, (weights k p : ℝ) * monomial (flat A) p := by
  unfold weightedPolynomial representativeReal representative
  push_cast
  congr 1
  ext p
  ring

/-- The support family retains every row/column orbit of the 73 primitives. -/
def circuitFamily : Set (PermIndex → ℝ) :=
  {y | ∃ k : Fin 73, ∃ g : Relabel, y = movedVector g (primitiveReal k)}

theorem circuitFamily_nonempty : circuitFamily.Nonempty :=
  ⟨movedVector 1 (primitiveReal 0), 0, 1, rfl⟩

theorem circuitFamily_kernel (y : PermIndex → ℝ) (hy : y ∈ circuitFamily) : Kernel y := by
  rcases hy with ⟨k,g,rfl⟩
  exact kernel_movedVector g (Census.primitive_kernel k)

/-- The only remaining premises here are the separately kernel-checked census
coverage theorem and the 131 explicit Gram inequalities. -/
theorem strongQuarticBound_of_gram_cover
    (hcover : ∀ x : PermIndex → ℝ, Kernel x → x ≠ 0 →
      ∃ k : Fin 73, ∃ g : Relabel,
        movedVector g (primitiveReal k) ≠ 0 ∧
        Circuit.SupportedIn (movedVector g (primitiveReal k)) x)
    (hgram : ∀ k : Fin 131, ∀ a : Cell → ℝ,
      (∑ p : PermIndex, (weights k p : ℝ) * monomial a p) + defect a / 4000 ≤
        3/32 * (∑ j : Cell, a j ^ 2)^2) : StrongQuarticBound := by
  have hrep : ∀ k : Fin 131, ∀ A : Rows,
      weightedPolynomial (representativeReal k) A ≤ quarticTarget A - defect (flat A) / 4000 := by
    intro k A
    rw [weightedPolynomial_representative]
    have h := hgram k (flat A)
    change _ ≤ quarticTarget A at h
    exact le_sub_iff_add_le.mpr h
  have hprimitive : ∀ k : Fin 73, ∀ A : Rows,
      weightedPolynomial ((2 / Circuit.mass (primitiveReal k)) • primitiveReal k) A ≤
        quarticTarget A - defect (flat A) / 4000 ∧
      weightedPolynomial (-((2 / Circuit.mass (primitiveReal k)) • primitiveReal k)) A ≤
        quarticTarget A - defect (flat A) / 4000 := by
    intro k A
    constructor
    · rw [primitive_normalized_positive, weightedPolynomial_moved]
      have h := hrep (Census.positiveGram k) (relabelRows (Census.relabel (Census.positiveRelabel k)) A)
      simpa only [quarticTarget_relabel, defect_relabel] using h
    · rw [primitive_normalized_negative, weightedPolynomial_moved]
      have h := hrep (Census.negativeGram k) (relabelRows (Census.relabel (Census.negativeRelabel k)) A)
      simpa only [quarticTarget_relabel, defect_relabel] using h
  have hfamily : ∀ y ∈ circuitFamily, ∀ A : Rows,
      weightedPolynomial ((2 / Circuit.mass y) • y) A ≤ quarticTarget A - defect (flat A) / 4000 ∧
      weightedPolynomial (-((2 / Circuit.mass y) • y)) A ≤ quarticTarget A - defect (flat A) / 4000 := by
    rintro y ⟨k,g,rfl⟩ A
    have hp := hprimitive k (relabelRows g A)
    have he (t : ℝ) : t • movedVector g (primitiveReal k) = movedVector g (t • primitiveReal k) := rfl
    have hn (z : PermIndex → ℝ) : -(movedVector g z) = movedVector g (-z) := rfl
    rw [mass_movedVector, he, hn, weightedPolynomial_moved, weightedPolynomial_moved]
    simpa only [quarticTarget_relabel, defect_relabel] using hp
  have hc : ∀ x, Kernel x → x ≠ 0 → ∃ y ∈ circuitFamily, y ≠ 0 ∧ Circuit.SupportedIn y x := by
    intro x hx hx0
    obtain ⟨k,g,hg,hs⟩ := hcover x hx hx0
    exact ⟨movedVector g (primitiveReal k), ⟨k,g,rfl⟩, hg, hs⟩
  have h := weightedPolynomial_bound_of_support_cover circuitFamily
    (fun A => quarticTarget A - defect (flat A) / 4000)
    circuitFamily_nonempty circuitFamily_kernel hc hfamily
  intro x hx hm A
  exact le_sub_iff_add_le.mp (h x hx hm A)

end
end FourRow
