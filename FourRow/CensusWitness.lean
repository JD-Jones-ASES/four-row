import FourRow.CensusWitnessData
import FourRow.CensusTables
import FourRow.CensusRelabel
namespace FourRow.Census
theorem extension_of_witness {i : Fin 5109} {p : PermIndex} (e : ExtensionWitness)
    (he : ValidExtension i p e) :
    (∃ g k, insert p (independentSupport i) = moved actionHom g (independentSupport k)) ∨
    (∃ g k, moved actionHom g (circuitSupport k) ⊆ insert p (independentSupport i)) := by
  rcases e with ⟨k,g⟩
  cases k with
  | inl k =>
    left
    refine ⟨relabel g,k,?_⟩
    have hh : ∀ q, q ∈ independentSupport k ↔
        action (relabel g) q ∈ insert p (independentSupport i) := by
      simpa only [ValidExtension,mem_independentSupport,Finset.mem_insert,literalAction_eq] using he
    ext q
    constructor
    · intro hq
      apply Finset.mem_image.mpr
      refine ⟨(action (relabel g)).symm q,?_,(action (relabel g)).apply_symm_apply q⟩
      apply (hh _).mpr
      simpa using hq
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨t,ht,rfl⟩
      exact (hh t).mp ht
  | inr k =>
    right
    refine ⟨relabel g,k,?_⟩
    have hh : ∀ q, q ∈ circuitSupport k →
        action (relabel g) q ∈ insert p (independentSupport i) := by
      simpa only [ValidExtension,mem_circuitSupport,mem_independentSupport,
        Finset.mem_insert,literalAction_eq] using he
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨t,ht,rfl⟩
    exact hh t ht
end FourRow.Census
