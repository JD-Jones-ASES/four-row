import FourRow.GramData
import FourRow.Relabel

namespace FourRow
open scoped BigOperators

/-- Exactly the twelve product constraints singled out by the Gram certificates. -/
def ProductRelations (A : Rows) : Prop :=
  (∀ i j k l, k ≠ l → A i k * A i l = A j k * A j l) ∧
  (∀ i j k l, i ≠ j → A i k * A j k = A i l * A j l)

private theorem three_products (a b c x y z : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hbc : 0 < b*c)
    (h1 : a*b = x*y) (h2 : a*c = x*z) (h3 : b*c = y*z) : a = x := by
  have hsq : a^2*(b*c) = x^2*(b*c) := by
    calc
      a^2*(b*c) = (a*b)*(a*c) := by ring
      _ = (x*y)*(x*z) := by rw [h1,h2]
      _ = x^2*(y*z) := by ring
      _ = x^2*(b*c) := by rw [h3]
  exact (sq_eq_sq₀ ha hx).mp (mul_right_cancel₀ (ne_of_gt hbc) hsq)

private theorem pos_of_nonneg_of_mul_pos {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (h : 0 < a*b) : 0 < a := by
  by_contra h'
  have : a = 0 := le_antisymm (le_of_not_gt h') ha
  simp [this] at h

/-- A product-constrained matrix with two positive entries in a row is positive everywhere. -/
theorem all_positive_of_two (A : Rows) (hA : NonnegativeRows A) (hR : ProductRelations A)
    (i k l : Row) (hkl : k ≠ l) (hk : 0 < A i k) (hl : 0 < A i l) :
    ∀ j q, 0 < A j q := by
  have hcol : ∀ j, 0 < A j k := by
    intro j
    have hp : 0 < A j k * A j l := by rw [← hR.1 i j k l hkl]; exact mul_pos hk hl
    exact pos_of_nonneg_of_mul_pos (hA j k) (hA j l) hp
  intro j q
  obtain ⟨s, hsj⟩ := exists_ne j
  have hp : 0 < A j q * A s q := by
    rw [← hR.2 j s k q (Ne.symm hsj)]
    exact mul_pos (hcol j) (hcol s)
  exact pos_of_nonneg_of_mul_pos (hA j q) (hA s q) hp

/-- Positive product-constrained matrices are constant. -/
theorem constant_of_positive (A : Rows) (hA : ∀ i j, 0 < A i j)
    (hR : ProductRelations A) : ∀ i j, A i j = A 0 0 := by
  have rows : ∀ i j k, A i k = A j k := by
    intro i j k
    fin_cases k
    · exact three_products _ _ _ _ _ _ (hA i 0).le (hA j 0).le
        (mul_pos (hA i 1) (hA i 2))
        (hR.1 i j 0 1 (by decide)) (hR.1 i j 0 2 (by decide)) (hR.1 i j 1 2 (by decide))
    · exact three_products _ _ _ _ _ _ (hA i 1).le (hA j 1).le
        (mul_pos (hA i 0) (hA i 2))
        (hR.1 i j 1 0 (by decide)) (hR.1 i j 1 2 (by decide)) (hR.1 i j 0 2 (by decide))
    · exact three_products _ _ _ _ _ _ (hA i 2).le (hA j 2).le
        (mul_pos (hA i 0) (hA i 1))
        (hR.1 i j 2 0 (by decide)) (hR.1 i j 2 1 (by decide)) (hR.1 i j 0 1 (by decide))
    · exact three_products _ _ _ _ _ _ (hA i 3).le (hA j 3).le
        (mul_pos (hA i 0) (hA i 1))
        (hR.1 i j 3 0 (by decide)) (hR.1 i j 3 1 (by decide)) (hR.1 i j 0 1 (by decide))
  intro i j
  rw [rows i 0 j]
  have hp := hR.2 0 1 j 0 (by decide)
  rw [rows 1 0 j, rows 1 0 0] at hp
  exact (sq_eq_sq₀ (hA 0 j).le (hA 0 0).le).mp (by simpa [pow_two] using hp)


/-- Vanishing of the symmetric defect gives each of the twelve constraints. -/
theorem productRelations_of_defect_zero (A : Rows) (hz : defect (flat A) = 0) :
    ProductRelations A := by
  have hterm (i j k l : Row) :
      (if k = l then 0 else (A i k * A i l - A j k * A j l)^2) +
      (if i = j then 0 else (A i k * A j k - A i l * A j l)^2) = 0 := by
    have hn : ∀ i j k l : Row, 0 ≤
        (if k = l then 0 else (A i k * A i l - A j k * A j l)^2) +
        (if i = j then 0 else (A i k * A j k - A i l * A j l)^2) := by
      intros; positivity
    simp only [defect, flat_cell] at hz
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
        Finset.sum_nonneg fun l _ => hn i j k l)).mp hz i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hn i j k l)).mp
      h1 j (Finset.mem_univ j)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Finset.sum_nonneg fun l _ => hn i j k l)).mp h2 k (Finset.mem_univ k)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn i j k l)).mp h3 l (Finset.mem_univ l)
  constructor
  · intro i j k l hkl
    have h := hterm i j k l
    simp only [ite_eq_right hkl] at h
    have : 0 ≤ (if i = j then (0:ℝ) else (A i k*A j k-A i l*A j l)^2) := by positivity
    have hs : (A i k*A i l-A j k*A j l)^2 = 0 := by nlinarith [sq_nonneg (A i k*A i l-A j k*A j l)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro i j k l hij
    have h := hterm i j k l
    simp only [ite_eq_right hij] at h
    have : 0 ≤ (if k = l then (0:ℝ) else (A i k*A i l-A j k*A j l)^2) := by positivity
    have hs : (A i k*A j k-A i l*A j l)^2 = 0 := by nlinarith [sq_nonneg (A i k*A j k-A i l*A j l)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- Complete normalized classification of nonnegative product-constrained rows. -/
theorem normalized_product_classification (A : Rows) (hA : NonnegativeRows A)
    (hn : NormalizedRows A) (hR : ProductRelations A) :
    (∀ i j, A i j = 1) ∨ (∃ τ : Perm4, ∀ i j, A i j = if j = τ i then 2 else 0) := by
  classical
  by_cases ht : ∃ i k l, k ≠ l ∧ 0 < A i k ∧ 0 < A i l
  · obtain ⟨i,k,l,hkl,hk,hl⟩ := ht
    have hp := all_positive_of_two A hA hR i k l hkl hk hl
    have hc := constant_of_positive A hp hR
    have hnorm := hn 0
    have hsq : (A 0 0)^2 = 1 := by
      simp only [hc, Fin.sum_univ_succ] at hnorm
      norm_num at hnorm
      nlinarith
    have hone : A 0 0 = 1 := (sq_eq_sq₀ (hA 0 0) (by norm_num)).mp (by simpa using hsq)
    exact Or.inl (fun i j => (hc i j).trans hone)
  · have hp : ∀ i, ∃ j, 0 < A i j := by
      intro i
      by_contra h
      push Not at h
      have hz : ∀ j, A i j = 0 := fun j => le_antisymm (h j) (hA i j)
      have hnorm := hn i
      simp [hz] at hnorm
    choose f hf using hp
    have hz : ∀ i j, j ≠ f i → A i j = 0 := by
      intro i j hj
      apply le_antisymm _ (hA i j)
      apply le_of_not_gt
      intro hpos
      exact ht ⟨i, f i, j, Ne.symm hj, hf i, hpos⟩
    have hinj : Function.Injective f := by
      intro i j heq
      by_contra hij
      obtain ⟨k,hk⟩ := exists_ne (f i)
      have hprod := hR.2 i j (f i) k hij
      have hpos : 0 < A i (f i)*A j (f i) := by rw [heq]; exact mul_pos (heq ▸ hf i) (hf j)
      rw [hz i k hk, zero_mul] at hprod
      linarith
    let τ : Perm4 := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
    have hval : ∀ i, A i (f i) = 2 := by
      intro i
      have hsum : (∑ j, A i j ^ 2) = A i (f i) ^ 2 := by
        apply Finset.sum_eq_single (f i)
        · intro j _ hj; simp [hz i j hj]
        · simp
      have hnorm := hn i
      rw [hsum] at hnorm
      apply (sq_eq_sq₀ (hA i (f i)) (by norm_num)).mp
      nlinarith
    refine Or.inr ⟨τ, ?_⟩
    intro i j
    change A i j = if j = f i then 2 else 0
    by_cases hj : j = f i
    · simp [hj, hval]
    · simp [hj, hz i j hj]

end FourRow
