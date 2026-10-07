import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Literal lexicographic indexing of the four-row problem. -/
namespace FourRow

abbrev Row := Fin 4
abbrev PermIndex := Fin 24
abbrev Cell := Fin 16
abbrev Perm4 := Equiv.Perm Row

/-- The 24 permutations, in the order used by the evidence files. -/
def permutation : PermIndex → Row → Row := ![
  ![0,1,2,3], ![0,1,3,2], ![0,2,1,3], ![0,2,3,1], ![0,3,1,2], ![0,3,2,1],
  ![1,0,2,3], ![1,0,3,2], ![1,2,0,3], ![1,2,3,0], ![1,3,0,2], ![1,3,2,0],
  ![2,0,1,3], ![2,0,3,1], ![2,1,0,3], ![2,1,3,0], ![2,3,0,1], ![2,3,1,0],
  ![3,0,1,2], ![3,0,2,1], ![3,1,0,2], ![3,1,2,0], ![3,2,0,1], ![3,2,1,0]]

theorem permutation_bijective (p : PermIndex) : Function.Bijective (permutation p) := by
  fin_cases p <;> decide

def inverseIndex : PermIndex → PermIndex := ![0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]

def permEquiv (p : PermIndex) : Perm4 where
  toFun := permutation p
  invFun := permutation (inverseIndex p)
  left_inv := by fin_cases p <;> decide
  right_inv := by fin_cases p <;> decide

@[simp] theorem permEquiv_apply (p : PermIndex) (i : Row) : permEquiv p i = permutation p i := rfl

theorem permEquiv_bijective : Function.Bijective permEquiv := by
  constructor
  · intro p q h
    have hfun : permutation p = permutation q := congrArg (fun e : Perm4 => e.toFun) h
    exact (show Function.Injective permutation by decide) hfun
  · have hall : ∀ σ : Perm4, ∃ p : PermIndex, ∀ i : Row, permutation p i = σ i := by decide
    intro σ
    obtain ⟨p, hp⟩ := hall σ
    exact ⟨p, Equiv.ext hp⟩

def indexOfPerm (σ : Perm4) : PermIndex :=
  if σ = permEquiv 0 then 0 else
  if σ = permEquiv 1 then 1 else
  if σ = permEquiv 2 then 2 else
  if σ = permEquiv 3 then 3 else
  if σ = permEquiv 4 then 4 else
  if σ = permEquiv 5 then 5 else
  if σ = permEquiv 6 then 6 else
  if σ = permEquiv 7 then 7 else
  if σ = permEquiv 8 then 8 else
  if σ = permEquiv 9 then 9 else
  if σ = permEquiv 10 then 10 else
  if σ = permEquiv 11 then 11 else
  if σ = permEquiv 12 then 12 else
  if σ = permEquiv 13 then 13 else
  if σ = permEquiv 14 then 14 else
  if σ = permEquiv 15 then 15 else
  if σ = permEquiv 16 then 16 else
  if σ = permEquiv 17 then 17 else
  if σ = permEquiv 18 then 18 else
  if σ = permEquiv 19 then 19 else
  if σ = permEquiv 20 then 20 else
  if σ = permEquiv 21 then 21 else
  if σ = permEquiv 22 then 22 else
  23

theorem indexOfPerm_permEquiv : Function.LeftInverse indexOfPerm permEquiv := by
  decide

def lexEquiv : PermIndex ≃ Perm4 where
  toFun := permEquiv
  invFun := indexOfPerm
  left_inv := indexOfPerm_permEquiv
  right_inv := by
    intro σ
    obtain ⟨p,rfl⟩ := permEquiv_bijective.2 σ
    exact congrArg permEquiv (indexOfPerm_permEquiv p)


/-- Row/column relabelings. The inverse on the row side gives a left action. -/
abbrev Relabel := Perm4 × Perm4

def action (g : Relabel) : Equiv.Perm PermIndex :=
  lexEquiv.trans ((Equiv.mulLeft g.2).trans ((Equiv.mulRight g.1⁻¹).trans lexEquiv.symm))

def incidence (i j : Row) (p : PermIndex) : ℤ := if permutation p i = j then 1 else 0

def cell (i j : Row) : Cell := ⟨4 * i.val + j.val, by omega⟩

def monomial (a : Cell → ℝ) (p : PermIndex) : ℝ := ∏ i : Row, a (cell i (permutation p i))

def Kernel (x : PermIndex → ℝ) : Prop := ∀ i j : Row,
  ∑ p : PermIndex, (incidence i j p : ℝ) * x p = 0

end FourRow
