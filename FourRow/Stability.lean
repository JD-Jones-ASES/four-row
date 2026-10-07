import FourRow.Definitions
import FourRow.Uniform

/-! Sharp stability follows from the separately checked endpoint bound and
an exact radial decomposition of every real balanced law in the closed ball. -/
namespace FourRow
noncomputable section

private theorem atom_abs_le_half_l1 {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hx : ∑ a, x a = 0) (a : α) :
    |x a| ≤ (∑ b, |x b|)/2 := by
  have hsum := Finset.sum_erase_add (s := Finset.univ) x (Finset.mem_univ a)
  have habs := Finset.sum_erase_add (s := Finset.univ) (fun b => |x b|) (Finset.mem_univ a)
  have he : ∑ b ∈ Finset.univ.erase a, x b = -x a := by linarith only [hsum,hx]
  have hb := Finset.abs_sum_le_sum_abs x (Finset.univ.erase a)
  rw [he,abs_neg] at hb
  linarith only [habs,hb]

/-- A single deviation from a probability law is at most total variation. -/
theorem atom_deviation_le (ν : Law) (hν : Probability ν) (σ : Perm4) :
    |ν σ - uniformLaw σ| ≤ tvDistance ν := by
  unfold tvDistance
  apply atom_abs_le_half_l1 (fun τ : Perm4 => ν τ - uniformLaw τ) ?_ σ
  rw [Finset.sum_sub_distrib,hν.mass,uniform_probability.mass,sub_self]

/-- Radius zero consists exactly of the uniform law. -/
theorem eq_uniform_of_zero_radius (ν : Law) (hν : InBall ν 0) : ν = uniformLaw := by
  funext σ
  have h := atom_deviation_le ν hν.probability σ
  have he : |ν σ - uniformLaw σ| = 0 := by
    linarith [abs_nonneg (ν σ - uniformLaw σ),hν.distance]
  exact sub_eq_zero.mp (abs_eq_zero.mp he)

def radialEndpoint (ν : Law) (r : ℝ) : Law :=
  fun σ => uniformLaw σ + (ν σ - uniformLaw σ)/(24*r)

/-- The extrapolated endpoint is a probability law; no positivity hypothesis
on individual atoms of the original law is strengthened. -/
theorem radialEndpoint_inBall (ν : Law) (r : ℝ) (hr : 0 < r)
    (hν : InBall ν r) : InBall (radialEndpoint ν r) (1/24) := by
  have ha : 0 < 24*r := by positivity
  have hmassdiff : ∑ σ, (ν σ-uniformLaw σ) = 0 := by
    rw [Finset.sum_sub_distrib,hν.probability.mass,uniform_probability.mass,sub_self]
  constructor
  · constructor
    · intro σ
      have hb := atom_deviation_le ν hν.probability σ
      have hlo : -r ≤ ν σ-uniformLaw σ := by
        have hh := neg_abs_le (ν σ-uniformLaw σ)
        linarith [hν.distance]
      dsimp [radialEndpoint,uniformLaw] at *
      have ht : -(1/24:ℝ) ≤ (ν σ-1/24)/(24*r) :=
        (le_div_iff₀ ha).mpr (by nlinarith only [hlo])
      linarith only [ht]
    · simp only [radialEndpoint,Finset.sum_add_distrib,← Finset.sum_div,
        uniform_probability.mass,hmassdiff,zero_div,add_zero]
  · intro i j
    have hid (σ : Perm4) :
        (if σ i = j then radialEndpoint ν r σ else 0) =
        (if σ i = j then uniformLaw σ else 0) +
          ((if σ i = j then ν σ else 0)-(if σ i = j then uniformLaw σ else 0))/(24*r) := by
      split_ifs <;> simp [radialEndpoint]
    simp_rw [hid]
    rw [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_sub_distrib,
      hν.balanced i j,uniform_balanced i j]
    norm_num
  · have htv : tvDistance (radialEndpoint ν r) = tvDistance ν/(24*r) := by
      dsimp [tvDistance,radialEndpoint]
      simp only [add_sub_cancel_left,abs_div,abs_of_pos ha,← Finset.sum_div]
      ring
    rw [htv]
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hν.distance]

/-- Exact affine decomposition at radius r. -/
theorem radial_decomposition (ν : Law) (r : ℝ) (hr : 0 < r) (σ : Perm4) :
    ν σ = (1-24*r)*uniformLaw σ + 24*r*radialEndpoint ν r σ := by
  dsimp [radialEndpoint]
  have ha : 24*r ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The full closed-ball stability result, assuming only the separately
proved endpoint assertion. The premise is removed in the final API. -/
theorem stability_of_endpoint (hEndpoint : EndpointBound)
    (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) (hn : NormalizedRows A) :
    ((1-24*r)/9)*varianceSum A ≤ 1-expectation ν A := by
  have hu := uniformDeficit A hA hn
  rw [← uniform_expectation] at hu
  change varianceSum A / 9 ≤ 1 - expectation uniformLaw A at hu
  rcases eq_or_lt_of_le hr with he | hp
  · subst r
    rw [eq_uniform_of_zero_radius ν hν]
    norm_num at ⊢
    linarith only [hu]
  · have hE := hEndpoint (radialEndpoint ν r) (radialEndpoint_inBall ν r hp hν) A hA hn
    have hex : expectation ν A = (1-24*r)*expectation uniformLaw A +
        24*r*expectation (radialEndpoint ν r) A := by
      dsimp [expectation]
      simp_rw [radial_decomposition ν r hp]
      simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
    have hc : 0 ≤ 1-24*r := by linarith only [hrmax]
    have h1 := mul_nonneg hc (sub_nonneg.mpr hu)
    have h2 := mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hE)
    nlinarith only [hex,h1,h2]

end
end FourRow
