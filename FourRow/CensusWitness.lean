module

public import FourRow.CensusWitnessData
public import FourRow.CensusTables
public import FourRow.CensusRelabel

@[expose] public section

namespace FourRow.Census

theorem extension_of_witness {i : Fin 5109} {p : PermIndex} (e : ExtensionWitness)
    (he : ValidExtension i p e) :
    (∃ g k, insert p (independentSupport i) = moved actionHom g (independentSupport k)) ∨
    (∃ g k, moved actionHom g (circuitSupport k) ⊆ insert p (independentSupport i)) := by
  by_cases hp : p ∈ independentSupport i
  · left
    exact ⟨1,i,by simp [Finset.insert_eq_of_mem hp]⟩
  have hp' : ¬ (independentMasks.get i.val).testBit p.val :=
    fun h => hp ((mem_independentSupport i p).mpr h)
  rcases e with ⟨k,g⟩
  have hact : literalAction g = (action (relabel g) : PermIndex → PermIndex) :=
    funext (literalAction_eq g)
  cases k with
  | inl k =>
    left
    refine ⟨relabel g,k,?_⟩
    have hh : imageMask (literalAction g) (independentMasks.get k.val) = extendedMask i p := by
      simpa [ValidExtension,hp'] using he
    have hs := congrArg maskSupport hh
    simpa only [maskSupport_imageMask,maskSupport_extendedMask,independentSupport,
      moved,actionHom_apply,← hact] using hs.symm
  | inr k =>
    right
    refine ⟨relabel g,k,?_⟩
    have hh : imageMask (literalAction g) (circuitMasks.get k.val) &&& extendedMask i p =
        imageMask (literalAction g) (circuitMasks.get k.val) := by
      simpa [ValidExtension,hp'] using he
    have hs := maskSupport_subset_of_land_eq hh
    simpa only [maskSupport_imageMask,maskSupport_extendedMask,circuitSupport,
      moved,actionHom_apply,← hact] using hs
end FourRow.Census
