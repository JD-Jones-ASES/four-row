import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Real all-law reduction

A finite family of nonzero kernel vectors meeting every nonzero kernel support
suffices to check every real point in an ℓ¹ ball.  The reduction uses compactness
and extreme points; the finite census remains a separate, explicit hypothesis.
-/

namespace FourRow.Circuit

open scoped BigOperators
open Set

variable {ι : Type*} [Fintype ι]

noncomputable def mass (x : ι → ℝ) : ℝ := ∑ i, |x i|

@[simp] theorem mass_zero : mass (0 : ι → ℝ) = 0 := by simp [mass]

theorem mass_nonneg (x : ι → ℝ) : 0 ≤ mass x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_mass (x : ι → ℝ) (i : ι) : |x i| ≤ mass x :=
  Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem mass_pos {x : ι → ℝ} (hx : x ≠ 0) : 0 < mass x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact lt_of_lt_of_le (abs_pos.mpr hi) (abs_le_mass x i)

@[simp] theorem mass_smul (a : ℝ) (x : ι → ℝ) : mass (a • x) = |a| * mass x := by
  simp [mass, abs_mul, Finset.mul_sum]

theorem mass_add_le (x y : ι → ℝ) : mass (x + y) ≤ mass x + mass y := by
  simp only [mass, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => abs_add_le _ _

noncomputable def signed (x : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun y := ∑ i, (if 0 ≤ x i then (1 : ℝ) else -1) * y i
  map_add' y z := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem signed_self (x : ι → ℝ) : signed x x = mass x := by
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

/-- Coordinates outside the support are required to vanish. -/
def SupportedIn (y x : ι → ℝ) : Prop := ∀ i, x i = 0 → y i = 0

/-- A sufficiently short line in a supported direction stays in the same
closed orthant in both directions. -/
theorem exists_small_step [Nonempty ι] {x z : ι → ℝ} (hz : SupportedIn z x) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, |t * z i| ≤ |x i| := by
  classical
  let b : ι → ℝ := fun i => if x i = 0 then 1 else |x i| / (|z i| + 1)
  have hb : ∀ i, 0 < b i := by
    intro i
    dsimp [b]
    split_ifs with h
    · norm_num
    · exact div_pos (abs_pos.mpr h) (by positivity)
  let t := Finset.univ.inf' Finset.univ_nonempty b
  have ht : 0 < t := (Finset.lt_inf'_iff _).mpr fun i _ => hb i
  refine ⟨t, ht, fun i => ?_⟩
  by_cases hi : x i = 0
  · simp [hz i hi, hi]
  · have hti : t ≤ |x i| / (|z i| + 1) := by
      simpa [b, hi] using (Finset.inf'_le b (Finset.mem_univ i))
    have hmul : t * (|z i| + 1) ≤ |x i| :=
      (le_div_iff₀ (by positivity)).mp hti
    rw [abs_mul, abs_of_pos ht]
    nlinarith

/-- On a fixed closed orthant, the ℓ¹ norm is linear. -/
theorem mass_add_step {x z : ι → ℝ} {t : ℝ}
    (ht : ∀ i, |t * z i| ≤ |x i|) :
    mass (x + t • z) = mass x + t * signed x z := by
  rw [mass, mass, signed, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := ht i
  by_cases hi : 0 ≤ x i
  · rw [ite_eq_left hi, one_mul, abs_of_nonneg hi] at *
    rw [abs_of_nonneg (by have := neg_abs_le (t * z i); linarith)]
  · have hi' : x i < 0 := lt_of_not_ge hi
    rw [ite_eq_right hi, neg_one_mul, abs_of_neg hi'] at *
    rw [abs_of_nonpos (by have := le_abs_self (t * z i); linarith)]
    ring

/-- The compact feasible body. -/
def body (K : Submodule ℝ (ι → ℝ)) (r : ℝ) : Set (ι → ℝ) :=
  {x | x ∈ K ∧ mass x ≤ r}

theorem body_compact (K : Submodule ℝ (ι → ℝ)) (r : ℝ) : IsCompact (body K r) := by
  have hc : Continuous (mass (ι := ι)) := by
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).abs
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => -r) (fun _ => r))).of_isClosed_subset
    (K.closed_of_finiteDimensional.inter (isClosed_le hc continuous_const))
  intro x hx
  constructor <;> intro i
  · exact (abs_le.mp ((abs_le_mass x i).trans hx.2)).1
  · exact (abs_le.mp ((abs_le_mass x i).trans hx.2)).2

theorem body_convex (K : Submodule ℝ (ι → ℝ)) (r : ℝ) : Convex ℝ (body K r) := by
  intro x hx y hy a b ha hb hab
  refine ⟨K.add_mem (K.smul_mem a hx.1) (K.smul_mem b hy.1), ?_⟩
  calc
    mass (a • x + b • y) ≤ mass (a • x) + mass (b • y) := mass_add_le _ _
    _ = a * mass x + b * mass y := by rw [mass_smul, mass_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = r := by rw [← add_mul, hab, one_mul]

/-- A tangent vector supported on an extreme point must vanish. -/
theorem extreme_tangent_zero [Nonempty ι] {K : Submodule ℝ (ι → ℝ)} {r : ℝ}
    {x : ι → ℝ} (hx : x ∈ (body K r).extremePoints ℝ) {z : ι → ℝ}
    (hzK : z ∈ K) (hz : SupportedIn z x) (hs : signed x z = 0) : z = 0 := by
  obtain ⟨t, ht, hsmall⟩ := exists_small_step hz
  have hxK := hx.1.1
  have hxr := hx.1.2
  have hp : x + t • z ∈ body K r := by
    refine ⟨K.add_mem hxK (K.smul_mem t hzK), ?_⟩
    simpa [mass_add_step hsmall, hs] using hxr
  have hnsmall : ∀ i, |(-t) * z i| ≤ |x i| := by simpa using hsmall
  have hn : x + (-t) • z ∈ body K r := by
    refine ⟨K.add_mem hxK (K.smul_mem (-t) hzK), ?_⟩
    rw [mass_add_step hnsmall, hs, mul_zero, add_zero]
    exact hxr
  have hmid : midpoint ℝ (x + t • z) (x + (-t) • z) = x := by
    ext i
    simp [midpoint, AffineMap.lineMap_apply, smul_eq_mul]
    ring
  have hseg : x ∈ openSegment ℝ (x + t • z) (x + (-t) • z) := by
    simpa only [hmid] using midpoint_mem_openSegment (𝕜 := ℝ) (x + t • z) (x + (-t) • z)
  have heq := hx.2 hp hn hseg
  ext i
  have hi := congrFun heq i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.zero_apply]
  exact (mul_eq_zero.mp (by linarith : t * z i = 0)).resolve_left (ne_of_gt ht)

/-- Every supported kernel vector at a nonzero extreme point is a scalar multiple
of that point.  No rationality assumption enters this real theorem. -/
theorem extreme_supported_eq_smul [Nonempty ι] {K : Submodule ℝ (ι → ℝ)} {r : ℝ}
    {x : ι → ℝ} (hx : x ∈ (body K r).extremePoints ℝ) (hx0 : x ≠ 0)
    {y : ι → ℝ} (hyK : y ∈ K) (hy : SupportedIn y x) :
    y = (signed x y / mass x) • x := by
  have hm : mass x ≠ 0 := ne_of_gt (mass_pos hx0)
  have hz : y - (signed x y / mass x) • x = 0 := by
    apply extreme_tangent_zero hx (K.sub_mem hyK (K.smul_mem _ hx.1.1))
    · intro i hi
      simp [hi, hy i hi]
    · simp [map_sub, map_smul, hm]
  exact sub_eq_zero.mp hz

/-- Transfer an absolute homogeneous linear bound from any support-covering
family of kernel vectors to every real point of the closed ℓ¹ ball.

The support coverage premise is where the finite, kernel-checked census plugs
in.  In particular it is not enough merely to check the listed vectors. -/
theorem linear_bound_of_support_cover [Nonempty ι]
    (K : Submodule ℝ (ι → ℝ)) (C : Set (ι → ℝ))
    (hK : ∀ y ∈ C, y ∈ K)
    (hcover : ∀ x ∈ K, x ≠ 0 → ∃ y ∈ C, y ≠ 0 ∧ SupportedIn y x)
    (L : (ι → ℝ) →ₗ[ℝ] ℝ) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbound : ∀ y ∈ C, |L y| ≤ c * mass y)
    {x : ι → ℝ} (hx : x ∈ body K r) : L x ≤ c * r := by
  have hext : (body K r).extremePoints ℝ ⊆ {x | L x ≤ c * r} := by
    intro z hz
    by_cases hz0 : z = 0
    · simpa [hz0] using mul_nonneg hc hr
    obtain ⟨y, hyC, hy0, hys⟩ := hcover z hz.1.1 hz0
    let a := signed z y / mass z
    have hyeq : y = a • z := extreme_supported_eq_smul hz hz0 (hK y hyC) hys
    have ha : a ≠ 0 := by
      intro h
      apply hy0
      simp [h] at hyeq
      exact hyeq
    have habs : 0 < |a| := abs_pos.mpr ha
    have hh := hbound y hyC
    rw [hyeq, map_smul, smul_eq_mul, abs_mul, mass_smul] at hh
    have hrate : |L z| ≤ c * mass z := by
      apply (mul_le_mul_iff_right₀ habs).mp
      nlinarith only [hh]
    exact (le_abs_self _).trans (hrate.trans (mul_le_mul_of_nonneg_left hz.1.2 hc))
  have hconv : Convex ℝ {z | L z ≤ c * r} := (convex_Iic (c * r)).linear_preimage L
  have hclosed : IsClosed {z | L z ≤ c * r} :=
    isClosed_le L.continuous_of_finiteDimensional continuous_const
  have hsub : body K r ⊆ {z | L z ≤ c * r} := by
    rw [← closure_convexHull_extremePoints (body_compact K r) (body_convex K r)]
    exact closure_minimal (convexHull_min hext hconv) hclosed
  exact hsub hx

/-- The same reduction in the normalized-circuit interface used by the
endpoint Gram certificates. Both signs are required explicitly. -/
theorem linear_bound_of_normalized_support_cover [Nonempty ι]
    (K : Submodule ℝ (ι → ℝ)) (C : Set (ι → ℝ))
    (hK : ∀ y ∈ C, y ∈ K)
    (hcover : ∀ x ∈ K, x ≠ 0 → ∃ y ∈ C, y ≠ 0 ∧ SupportedIn y x)
    (L : (ι → ℝ) →ₗ[ℝ] ℝ) {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r)
    (hbound : ∀ y ∈ C, L ((r / mass y) • y) ≤ b ∧
      -L ((r / mass y) • y) ≤ b)
    {x : ι → ℝ} (hx : x ∈ body K r) : L x ≤ b := by
  have heach : ∀ y ∈ C, |L y| ≤ (b / r) * mass y := by
    intro y hyC
    by_cases hy0 : y = 0
    · simp [hy0]
    have hm := mass_pos hy0
    have h := hbound y hyC
    have h' : |L ((r / mass y) • y)| ≤ b := abs_le.mpr ⟨by linarith [h.2], h.1⟩
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (div_pos hr hm)] at h'
    apply (mul_le_mul_iff_left₀ hr).mp
    calc
      |L y| * r = (r / mass y * |L y|) * mass y := by field_simp
      _ ≤ b * mass y := mul_le_mul_of_nonneg_right h' hm.le
      _ = ((b / r) * mass y) * r := by field_simp
  have h := linear_bound_of_support_cover K C hK hcover L (div_nonneg hb hr.le)
    hr.le heach hx
  simpa [div_mul_cancel₀ b (ne_of_gt hr)] using h

end FourRow.Circuit
