module

public import FourRow.Finite
public import FourRow.Definitions
public import FourRow.Circuit

@[expose] public section

namespace FourRow
noncomputable section

theorem lexEquiv_apply (p : PermIndex) : lexEquiv p = permEquiv p := rfl

@[simp] theorem action_lex (g : Relabel) (p : PermIndex) :
    lexEquiv (action g p) = g.2 * lexEquiv p * g.1⁻¹ := by
  simp [action, Equiv.trans_apply]

@[simp] theorem action_permutation (g : Relabel) (p : PermIndex) (i : Row) :
    permutation (action g p) i = g.2 (permutation p (g.1⁻¹ i)) := by
  have h := congrArg (fun σ : Perm4 => σ i) (action_lex g p)
  exact h

def actionHom : Relabel →* Equiv.Perm PermIndex where
  toFun := action
  map_one' := by
    apply Equiv.ext
    intro p
    apply lexEquiv.injective
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro p
    apply lexEquiv.injective
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, action_lex, Prod.snd_mul,
      Prod.fst_mul, mul_inv_rev]
    group

@[simp] theorem actionHom_apply (g : Relabel) : actionHom g = action g := rfl

theorem incidence_action (g : Relabel) (i j : Row) (p : PermIndex) :
    incidence i j (action g p) = incidence (g.1⁻¹ i) (g.2⁻¹ j) p := by
  classical
  simp only [incidence, action_permutation]
  have heq : g.2 (permutation p (g.1⁻¹ i)) = j ↔ permutation p (g.1⁻¹ i) = g.2⁻¹ j :=
    ⟨fun h => by simpa using congrArg (fun k : Row => g.2⁻¹ k) h,
      fun h => by simpa using congrArg g.2 h⟩
  simp only [heq]

/-- Relabel a signed law by its permutation-coordinate action. -/
def movedVector (g : Relabel) (x : PermIndex → ℝ) : PermIndex → ℝ :=
  fun p => x ((action g).symm p)

theorem kernel_movedVector (g : Relabel) {x : PermIndex → ℝ} (hx : Kernel x) :
    Kernel (movedVector g x) := by
  intro i j
  rw [← Equiv.sum_comp (action g)]
  simpa [movedVector, incidence_action] using hx (g.1⁻¹ i) (g.2⁻¹ j)

theorem mass_movedVector (g : Relabel) (x : PermIndex → ℝ) :
    Circuit.mass (movedVector g x) = Circuit.mass x := by
  exact Equiv.sum_comp (action g).symm (fun p => |x p|)

def relabelRows (g : Relabel) (A : Rows) : Rows := fun i j => A (g.1 i) (g.2 j)

def flat (A : Rows) (k : Cell) : ℝ :=
  A ⟨k.val / 4, by omega⟩ ⟨k.val % 4, by omega⟩

@[simp] theorem flat_cell (A : Rows) (i j : Row) : flat A (cell i j) = A i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem monomial_flat (A : Rows) (p : PermIndex) :
    monomial (flat A) p = ∏ i : Row, A i (permutation p i) := by simp [monomial]

theorem monomial_action (g : Relabel) (A : Rows) (p : PermIndex) :
    monomial (flat A) (action g p) = monomial (flat (relabelRows g A)) p := by
  simp only [monomial_flat, action_permutation, relabelRows]
  rw [← Equiv.prod_comp g.1]
  simp

theorem sum_squares_flat (A : Rows) :
    ∑ k : Cell, flat A k ^ 2 = ∑ i : Row, ∑ j : Row, A i j ^ 2 := by
  simp [flat, Fin.sum_univ_succ]
  ring

theorem sum_squares_relabel (g : Relabel) (A : Rows) :
    ∑ k : Cell, flat (relabelRows g A) k ^ 2 = ∑ k : Cell, flat A k ^ 2 := by
  simp only [sum_squares_flat, relabelRows]
  calc
    _ = ∑ i : Row, ∑ j : Row, A (g.1 i) j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp g.2 (fun j => A (g.1 i) j ^ 2)
    _ = _ := Equiv.sum_comp g.1 (fun i => ∑ j : Row, A i j ^ 2)

theorem weighted_monomial_moved (g : Relabel) (x : PermIndex → ℝ) (A : Rows) :
    ∑ p, movedVector g x p * monomial (flat A) p =
      ∑ p, x p * monomial (flat (relabelRows g A)) p := by
  rw [← Equiv.sum_comp (action g)]
  simp [movedVector, monomial_action]

end
end FourRow
