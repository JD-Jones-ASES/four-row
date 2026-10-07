import FourRow.Finite
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Soundness lemmas for a proof-carrying support-extension census.

The support closure table is only combinatorial. All rank decisions are
replaced by explicit left inverses, so no modular elimination algorithm is
inside the trusted statement.
-/
namespace FourRow.Census

section Closure
variable {ι G N C : Type*} [DecidableEq ι] [Group G]
variable (action : G →* Equiv.Perm ι)

def moved (g : G) (s : Finset ι) : Finset ι := s.image (action g)

@[simp] theorem moved_one (s : Finset ι) : moved action 1 s = s := by
  simp [moved]

@[simp] theorem moved_mul (g h : G) (s : Finset ι) :
    moved action (g*h) s = moved action g (moved action h s) := by
  simp [moved, Finset.image_image, Function.comp_def]

@[simp] theorem moved_insert (g : G) (a : ι) (s : Finset ι) :
    moved action g (insert ((action g).symm a) s) = insert a (moved action g s) := by
  simp [moved]

theorem moved_mono (g : G) {s t : Finset ι} (h : s ⊆ t) :
    moved action g s ⊆ moved action g t := Finset.image_subset_image h

/-- Finite extension closure covers every set by an independent orbit or by
    a contained circuit orbit. The indexing types need not be finite. -/
theorem extension_coverage
    (independent : N → Finset ι) (circuit : C → Finset ι)
    (empty : ∃ n, independent n = ∅)
    (step : ∀ n a, (∃ g k, insert a (independent n) = moved action g (independent k)) ∨
      (∃ g k, moved action g (circuit k) ⊆ insert a (independent n))) :
    ∀ s : Finset ι,
      (∃ g k, s = moved action g (independent k)) ∨
      (∃ g k, moved action g (circuit k) ⊆ s) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨n, hn⟩ := empty
    left
    exact ⟨1,n,by simp [hn]⟩
  | @insert a s ha ih =>
    rcases ih with ⟨g,n,hn⟩ | ⟨g,k,hk⟩
    · subst s
      rcases step n ((action g).symm a) with ⟨h,k,hk⟩ | ⟨h,k,hk⟩
      · left
        refine ⟨g*h,k,?_⟩
        rw [moved_mul, ← hk, moved_insert]
      · right
        refine ⟨g*h,k,?_⟩
        rw [moved_mul]
        simpa only [moved_insert] using moved_mono action g hk
    · right
      exact ⟨g,k,Finset.Subset.trans hk (Finset.subset_insert a s)⟩
end Closure

section Linear
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- An integer scaled left inverse proves real column independence. -/
theorem integer_left_inverse
    (B : κ → ι → ℤ) (L : ι → κ → ℤ) (d : ℤ) (hd : d ≠ 0)
    (hprod : ∀ i j, ∑ k, L i k * B k j = if i = j then d else 0)
    (x : ι → ℝ) (hx : ∀ k, ∑ j, (B k j : ℝ) * x j = 0) : x = 0 := by
  funext i
  have h := congrArg (fun v : κ → ℝ => ∑ k, (L i k : ℝ) * v k) (funext hx)
  simp only [mul_zero, Finset.sum_const_zero] at h
  have hreal : ∀ j, ∑ k, (L i k : ℝ) * (B k j : ℝ) = if i = j then (d : ℝ) else 0 := by
    intro j
    exact_mod_cast hprod i j
  simp_rw [Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simp_rw [← mul_assoc, ← Finset.sum_mul, hreal] at h
  simp only [ite_mul, zero_mul] at h
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hd)
end Linear
end FourRow.Census

namespace FourRow.Census

/-- A small rectangular column set with a scaled integer left inverse. -/
structure IndependentRecord where
  size : ℕ
  col : Fin size → PermIndex
  row : Fin size → Cell
  scale : ℤ
  leftInverse : Fin size → Fin size → ℤ
  dataMatrix : Fin size → Fin size → ℤ

namespace IndependentRecord

def support (c : IndependentRecord) : Finset PermIndex := Finset.univ.image c.col

def matrix (c : IndependentRecord) (i j : Fin c.size) : ℤ :=
  incidence ⟨(c.row i).val / 4, by omega⟩ ⟨(c.row i).val % 4, by omega⟩ (c.col j)

def Valid (c : IndependentRecord) : Prop := c.scale ≠ 0 ∧
  (∀ i j, c.dataMatrix i j = c.matrix i j) ∧
  ∀ i j, ∑ k, c.leftInverse i k * c.dataMatrix k j = if i = j then c.scale else 0

instance (c : IndependentRecord) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _))

theorem Valid.product {c : IndependentRecord} (hc : c.Valid) :
    ∀ i j, ∑ k, c.leftInverse i k * c.matrix k j = if i = j then c.scale else 0 := by
  simpa only [hc.2.1] using hc.2.2

theorem col_injective (c : IndependentRecord) (hc : c.Valid) : Function.Injective c.col := by
  intro i j hij
  by_contra hne
  have hs : c.scale = 0 := by
    calc
      c.scale = ∑ k, c.leftInverse i k * c.matrix k i := by simpa using (hc.product i i).symm
      _ = ∑ k, c.leftInverse i k * c.matrix k j := by simp only [matrix, hij]
      _ = 0 := by simpa [hne] using hc.product i j
  exact hc.1 hs

/-- Valid records are independent over the real numbers, including the empty set. -/
theorem kernel_eq_zero (c : IndependentRecord) (hc : c.Valid)
    (x : PermIndex → ℝ) (hx : Kernel x)
    (hxs : ∀ p, p ∉ c.support → x p = 0) : x = 0 := by
  have hinj := c.col_injective hc
  have hsel : ∀ i, ∑ j, (c.matrix i j : ℝ) * x (c.col j) = 0 := by
    intro i
    have heq := hx ⟨(c.row i).val / 4, by omega⟩ ⟨(c.row i).val % 4, by omega⟩
    change ∑ j, (incidence ⟨(c.row i).val / 4, by omega⟩ ⟨(c.row i).val % 4, by omega⟩ (c.col j) : ℝ) * x (c.col j) = 0
    rw [← Finset.sum_image (s := Finset.univ) (g := c.col)
      (f := fun p => (incidence ⟨(c.row i).val / 4, by omega⟩ ⟨(c.row i).val % 4, by omega⟩ p : ℝ) * x p)
      (fun j _ k _ h => hinj h)]
    change ∑ p ∈ c.support,
      (incidence ⟨(c.row i).val / 4, by omega⟩ ⟨(c.row i).val % 4, by omega⟩ p : ℝ) * x p = 0
    rw [Finset.sum_subset (Finset.subset_univ _) (by
      intro p _ hp
      simp [hxs p hp])]
    exact heq
  have hzero := integer_left_inverse c.matrix c.leftInverse c.scale hc.1 hc.product
    (fun j => x (c.col j)) hsel
  funext p
  by_cases hp : p ∈ c.support
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    exact congrFun hzero j
  · exact hxs p hp
end IndependentRecord
end FourRow.Census

namespace FourRow.Census

def IndependentSupport (S : Finset PermIndex) : Prop :=
  ∀ x : PermIndex → ℝ, Kernel x → (∀ p, p ∉ S → x p = 0) → x = 0


end FourRow.Census
