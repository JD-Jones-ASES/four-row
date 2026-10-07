module

public import FourRow.Sharpness

@[expose] public section

/-! A human-facing description of the sharpness family, independent of the
lexicographic indexing used to check it. -/
namespace FourRow
noncomputable section

/-- Perturb uniform measure by one half of the identity atom, one half of
uniform measure on the nine derangements, minus uniform measure on the six
transpositions. In S₄ these classes have respectively four, zero, and two
fixed points. -/
def extremalLaw (r : ℝ) : Law := fun σ => 1/((24 : ℕ) : ℝ) + r *
  (if (Finset.univ.filter (fun i : Row => σ i = i)).card = 4 then 1/((2 : ℕ) : ℝ)
   else if (Finset.univ.filter (fun i : Row => σ i = i)).card = 0 then 1/((18 : ℕ) : ℝ)
   else if (Finset.univ.filter (fun i : Row => σ i = i)).card = 2 then -1/((6 : ℕ) : ℝ)
   else 0)

theorem extremalLaw_eq_sharpLaw (r : ℝ) : extremalLaw r = sharpLaw r := by
  funext σ
  obtain ⟨p,rfl⟩ := lexEquiv.surjective σ
  simp only [sharpLaw,Equiv.symm_apply_apply]
  have hu : (Finset.univ : Finset Row) = {0,1,2,3} := by decide
  fin_cases p <;>
    norm_num [extremalLaw,sharpTrade,lexEquiv,permEquiv,permutation,Fin.sum_univ_succ,
      hu, Finset.filter_insert, Finset.filter_singleton]

/-- The explicit family realizes the optimal stability coefficient at every
radius in the theorem and remains a genuine probability law up to radius 1/4. -/
theorem extremal_family (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/4) :
    InBall (extremalLaw r) r ∧ tvDistance (extremalLaw r) = r ∧
    NonnegativeRows sharpRows ∧ NormalizedRows sharpRows ∧ varianceSum sharpRows = 3 ∧
    expectation (extremalLaw r) sharpRows = 2/3+8*r := by
  rw [extremalLaw_eq_sharpLaw]
  exact ⟨sharpLaw_inBall r hr hrmax,sharpLaw_distance r hr,sharpRows_nonnegative,
    sharpRows_normalized,sharpRows_variance,sharpLaw_expectation r⟩

end
end FourRow
