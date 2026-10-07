import FourRow.Symmetry

/-! Assembly of the closed real endpoint from the support-cover census and
quartic inequalities. -/
namespace FourRow
noncomputable section
open scoped BigOperators

/-- The sixteen exact zero-marginal equations as a real linear subspace. -/
def kernelSpace : Submodule ℝ (PermIndex → ℝ) where
  carrier := {x | Kernel x}
  zero_mem' := by simp [Kernel]
  add_mem' := by
    intro x y hx hy i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx i j, hy i j, add_zero]
  smul_mem' := by
    intro c x hx i j
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      _ = c * ∑ p, (incidence i j p : ℝ) * x p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = 0 := by rw [hx i j, mul_zero]

/-- The quartic form linear in the signed law. -/
def lawFunctional (A : Rows) : (PermIndex → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ p, x p * monomial (flat A) p
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

def quarticTarget (A : Rows) : ℝ := 3/32 * (∑ k : Cell, flat A k ^ 2)^2

def basePolynomial (A : Rows) : ℝ := ∑ p : PermIndex, monomial (flat A) p

def weightedPolynomial (x : PermIndex → ℝ) (A : Rows) : ℝ :=
  ∑ p, (1 + x p) * monomial (flat A) p

theorem weightedPolynomial_split (x : PermIndex → ℝ) (A : Rows) :
    weightedPolynomial x A = basePolynomial A + lawFunctional A x := by
  simp [weightedPolynomial, basePolynomial, lawFunctional, add_mul, Finset.sum_add_distrib]

/-- Quartic inequality over every real point of the entire closed law ball. -/
def QuarticBound : Prop := ∀ x : PermIndex → ℝ, Kernel x → Circuit.mass x ≤ 2 →
  ∀ A : Rows, weightedPolynomial x A ≤ quarticTarget A

/-- Generic endpoint assembly: exhaustive support coverage and both normalized
signs imply the full real closed-ball quartic inequality. -/
theorem weightedPolynomial_bound_of_support_cover (C : Set (PermIndex → ℝ))
    (target : Rows → ℝ)
    (hne : C.Nonempty) (hK : ∀ y ∈ C, Kernel y)
    (hcover : ∀ x, Kernel x → x ≠ 0 → ∃ y ∈ C, y ≠ 0 ∧ Circuit.SupportedIn y x)
    (hgram : ∀ y ∈ C, ∀ A : Rows,
      weightedPolynomial ((2 / Circuit.mass y) • y) A ≤ target A ∧
      weightedPolynomial (-((2 / Circuit.mass y) • y)) A ≤ target A) :
    ∀ x : PermIndex → ℝ, Kernel x → Circuit.mass x ≤ 2 →
      ∀ A : Rows, weightedPolynomial x A ≤ target A := by
  intro x hx hm A
  have hb : 0 ≤ target A - basePolynomial A := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨hp, hn⟩ := hgram y hy A
    rw [weightedPolynomial_split] at hp hn
    simp only [map_neg] at hn
    linarith
  have hcert : ∀ y ∈ C,
      lawFunctional A ((2 / Circuit.mass y) • y) ≤ target A - basePolynomial A ∧
      -lawFunctional A ((2 / Circuit.mass y) • y) ≤ target A - basePolynomial A := by
    intro y hy
    obtain ⟨hp, hn⟩ := hgram y hy A
    rw [weightedPolynomial_split] at hp hn
    simp only [map_neg] at hn
    constructor <;> linarith
  have h := Circuit.linear_bound_of_normalized_support_cover kernelSpace C hK hcover
    (lawFunctional A) hb (by norm_num : (0 : ℝ) < 2) hcert (show x ∈ Circuit.body kernelSpace 2 from ⟨hx,hm⟩)
  rw [weightedPolynomial_split]
  linarith

/-- The usual quartic target is a specialization of the general transfer. -/
theorem quarticBound_of_support_cover (C : Set (PermIndex → ℝ))
    (hne : C.Nonempty) (hK : ∀ y ∈ C, Kernel y)
    (hcover : ∀ x, Kernel x → x ≠ 0 → ∃ y ∈ C, y ≠ 0 ∧ Circuit.SupportedIn y x)
    (hgram : ∀ y ∈ C, ∀ A : Rows,
      weightedPolynomial ((2 / Circuit.mass y) • y) A ≤ quarticTarget A ∧
      weightedPolynomial (-((2 / Circuit.mass y) • y)) A ≤ quarticTarget A) :
    QuarticBound :=
  weightedPolynomial_bound_of_support_cover C quarticTarget hne hK hcover hgram

/-- Center and rescale a probability law around the uniform law. -/
def shiftedLaw (ν : Law) (p : PermIndex) : ℝ := 24 * ν (lexEquiv p) - 1

theorem indexed_balance (ν : Law) (hν : Balanced ν) (i j : Row) :
    ∑ p : PermIndex, (incidence i j p : ℝ) * ν (lexEquiv p) = 1/4 := by
  have h := Equiv.sum_comp lexEquiv (fun σ : Perm4 => if σ i = j then ν σ else 0)
  have hs : (∑ p : PermIndex, (incidence i j p : ℝ) * ν (lexEquiv p)) =
      ∑ σ : Perm4, if σ i = j then ν σ else 0 := by
    rw [← h]
    apply Finset.sum_congr rfl
    intro p _
    simp [incidence, lexEquiv_apply]
    rfl
  rw [hs]
  exact hν i j

theorem shiftedLaw_kernel (ν : Law) (hν : Balanced ν) : Kernel (shiftedLaw ν) := by
  intro i j
  have hv := indexed_balance ν hν i j
  have hu := indexed_balance uniformLaw uniform_balanced i j
  have hid : ∑ p : PermIndex, (incidence i j p : ℝ) * shiftedLaw ν p =
      24 * ((∑ p : PermIndex, (incidence i j p : ℝ) * ν (lexEquiv p)) -
        ∑ p : PermIndex, (incidence i j p : ℝ) * uniformLaw (lexEquiv p)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
    apply Finset.sum_congr rfl
    intro p _
    simp only [shiftedLaw, uniformLaw]
    ring
  rw [hid, hv, hu]
  norm_num

theorem shiftedLaw_mass (ν : Law) : Circuit.mass (shiftedLaw ν) = 48 * tvDistance ν := by
  have h := Equiv.sum_comp lexEquiv (fun σ : Perm4 => |ν σ - uniformLaw σ|)
  rw [Circuit.mass, tvDistance, ← h]
  calc
    _ = ∑ p : PermIndex, 24 * |ν (lexEquiv p) - uniformLaw (lexEquiv p)| := by
      apply Finset.sum_congr rfl
      intro p _
      rw [shiftedLaw]
      have he : 24 * ν (lexEquiv p) - 1 = 24 * (ν (lexEquiv p) - uniformLaw (lexEquiv p)) := by
        simp only [uniformLaw]
        ring
      rw [he, abs_mul]
      norm_num
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem weightedPolynomial_shiftedLaw (ν : Law) (A : Rows) :
    weightedPolynomial (shiftedLaw ν) A = 24 * expectation ν A := by
  rw [expectation, weightedPolynomial, Finset.mul_sum, ← Equiv.sum_comp lexEquiv]
  apply Finset.sum_congr rfl
  intro p _
  simp only [shiftedLaw, monomial_flat, lexEquiv_apply, permEquiv_apply]
  ring

theorem quarticTarget_normalized (A : Rows) (hA : NormalizedRows A) : quarticTarget A = 24 := by
  have hi : ∀ i : Row, ∑ j : Row, A i j ^ 2 = 4 := by
    intro i
    have h := hA i
    linarith
  rw [quarticTarget, sum_squares_flat]
  simp [hi]
  norm_num

/-- The normalized probability-row-L² endpoint has arbitrary real laws and
nonnegative entries, with no strictness assumption. -/
theorem endpointBound_of_quarticBound (hquartic : QuarticBound) : EndpointBound := by
  intro ν hν A _ hA
  have hm : Circuit.mass (shiftedLaw ν) ≤ 2 := by
    rw [shiftedLaw_mass]
    have ht := hν.distance
    linarith
  have h := hquartic (shiftedLaw ν) (shiftedLaw_kernel ν hν.balanced) hm A
  rw [weightedPolynomial_shiftedLaw, quarticTarget_normalized A hA] at h
  linarith

/-- The positive Gram remainder retained for exact endpoint equality. -/
def StrongQuarticBound : Prop := ∀ x : PermIndex → ℝ, Kernel x → Circuit.mass x ≤ 2 →
  ∀ A : Rows, weightedPolynomial x A + defect (flat A) / 4000 ≤ quarticTarget A

theorem StrongQuarticBound.quarticBound (h : StrongQuarticBound) : QuarticBound := by
  intro x hx hm A
  have hd := defect_nonneg (flat A)
  have hb := h x hx hm A
  linarith

theorem normalized_defect_bound_of_strong (h : StrongQuarticBound)
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hn : NormalizedRows A) :
    24 * expectation ν A + defect (flat A) / 4000 ≤ 24 := by
  have hm : Circuit.mass (shiftedLaw ν) ≤ 2 := by
    rw [shiftedLaw_mass]
    have ht := hν.distance
    linarith
  have hb := h (shiftedLaw ν) (shiftedLaw_kernel ν hν.balanced) hm A
  rwa [weightedPolynomial_shiftedLaw, quarticTarget_normalized A hn] at hb

theorem defect_zero_of_endpoint_equality (h : StrongQuarticBound)
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hn : NormalizedRows A)
    (he : expectation ν A = 1) : defect (flat A) = 0 := by
  have hb := normalized_defect_bound_of_strong h ν hν A hn
  have hd := defect_nonneg (flat A)
  rw [he] at hb
  linarith

/-- Scaling each row scales the permutation expectation by the row-product. -/
theorem expectation_scale_rows (ν : Law) (A : Rows) (c : Row → ℝ) :
    expectation ν (fun i j => c i * A i j) = (∏ i, c i) * expectation ν A := by
  simp only [expectation, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

def rowSquareSum (A : Rows) (i : Row) : ℝ := ∑ j : Row, A i j ^ 2

theorem rowSquareSum_nonneg (A : Rows) (i : Row) : 0 ≤ rowSquareSum A i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem zero_row_of_squareSum (A : Rows) (i : Row) (h : rowSquareSum A i = 0) :
    ∀ j, A i j = 0 := by
  intro j
  have hj : A i j ^ 2 ≤ rowSquareSum A i :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
  rw [h] at hj
  nlinarith [sq_nonneg (A i j)]

theorem expectation_zero_row (ν : Law) (A : Rows) (i : Row) (h : ∀ j, A i j = 0) :
    expectation ν A = 0 := by
  apply Finset.sum_eq_zero
  intro σ _
  have hp : ∏ k : Row, A k (σ k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h (σ i))
  simp [hp]

theorem expectation_nonneg (ν : Law) (hν : Probability ν) (A : Rows) (hA : NonnegativeRows A) :
    0 ≤ expectation ν A := by
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (hν.nonneg σ) (Finset.prod_nonneg fun i _ => hA i (σ i))

/-- The square-root-free endpoint for all nonnegative real matrices, including
matrices with zero rows. This is equivalent to the probability-row-L² form. -/
theorem endpoint_algebraic_of_bound (hend : EndpointBound)
    (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256 * (expectation ν A)^2 ≤ ∏ i : Row, ∑ j : Row, A i j ^ 2 := by
  by_cases hz : ∃ i : Row, rowSquareSum A i = 0
  · obtain ⟨i,hi⟩ := hz
    rw [expectation_zero_row ν A i (zero_row_of_squareSum A i hi)]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact Finset.prod_nonneg fun i _ => rowSquareSum_nonneg A i
  have hs : ∀ i : Row, 0 < rowSquareSum A i := by
    intro i
    exact lt_of_le_of_ne (rowSquareSum_nonneg A i) (Ne.symm (fun h => hz ⟨i,h⟩))
  let q : Row → ℝ := fun i => Real.sqrt (rowSquareSum A i)
  have hq : ∀ i : Row, 0 < q i := fun i => Real.sqrt_pos.mpr (hs i)
  have hq2 : ∀ i : Row, (q i)^2 = rowSquareSum A i :=
    fun i => Real.sq_sqrt (hs i).le
  let c : Row → ℝ := fun i => 2 / q i
  let B : Rows := fun i j => c i * A i j
  have hBnonneg : NonnegativeRows B := by
    intro i j
    exact mul_nonneg (div_nonneg (by norm_num) (hq i).le) (hA i j)
  have hBnorm : NormalizedRows B := by
    intro i
    change (∑ j : Row, (c i * A i j)^2) / 4 = 1
    simp only [mul_pow, ← Finset.mul_sum]
    change ((2 / q i)^2 * rowSquareSum A i) / 4 = 1
    rw [div_pow, hq2]
    field_simp [ne_of_gt (hs i)]
    ring
  have hBE := hend ν hν B hBnonneg hBnorm
  have hBexpect : expectation ν B = (∏ i : Row, c i) * expectation ν A :=
    expectation_scale_rows ν A c
  have hqc : (∏ i : Row, c i) * ∏ i : Row, q i = 16 := by
    rw [← Finset.prod_mul_distrib]
    have he : ∀ i : Row, c i * q i = 2 := by
      intro i
      exact div_mul_cancel₀ 2 (ne_of_gt (hq i))
    norm_num [he]
  have hprodnonneg : 0 ≤ ∏ i : Row, q i := Finset.prod_nonneg fun i _ => (hq i).le
  have hnorm : 16 * expectation ν A ≤ ∏ i : Row, q i := by
    have h := mul_le_mul_of_nonneg_right hBE hprodnonneg
    rw [hBexpect] at h
    nlinarith [hqc]
  have hnonneg := expectation_nonneg ν hν.probability A hA
  have hsquare : (16 * expectation ν A)^2 ≤ (∏ i : Row, q i)^2 := by
    nlinarith
  have hprod : (∏ i : Row, q i)^2 = ∏ i : Row, ∑ j : Row, A i j ^ 2 := by
    rw [← Finset.prod_pow]
    simp only [hq2, rowSquareSum]
  rw [hprod] at hsquare
  nlinarith

end
end FourRow
