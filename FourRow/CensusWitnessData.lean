import FourRow.CensusTableData

namespace FourRow.Census
abbrev ExtensionWitness := (Fin 5109 ⊕ Fin 73) × Fin 576

/-- Pointwise bit checks avoid expensive repeated finite-set image construction. -/
def ValidExtension (i : Fin 5109) (p : PermIndex) (e : ExtensionWitness) : Prop :=
  match e.1 with
  | Sum.inl k => ∀ q : PermIndex,
      (independentMasks.get k.val).testBit q.val ↔
      literalAction e.2 q = p ∨ (independentMasks.get i.val).testBit (literalAction e.2 q).val
  | Sum.inr k => ∀ q : PermIndex,
      (circuitMasks.get k.val).testBit q.val →
      literalAction e.2 q = p ∨ (independentMasks.get i.val).testBit (literalAction e.2 q).val

instance (i : Fin 5109) (p : PermIndex) (e : ExtensionWitness) : Decidable (ValidExtension i p e) := by
  unfold ValidExtension
  cases e.1 <;> infer_instance

theorem mem_independentSupport (i : Fin 5109) (p : PermIndex) :
    p ∈ independentSupport i ↔ (independentMasks.get i.val).testBit p.val := by
  simp [independentSupport,maskSupport]

theorem mem_circuitSupport (i : Fin 73) (p : PermIndex) :
    p ∈ circuitSupport i ↔ (circuitMasks.get i.val).testBit p.val := by
  simp [circuitSupport,maskSupport]

end FourRow.Census
