module

public import FourRow.CensusMask

@[expose] public section

namespace FourRow.Census
abbrev ExtensionWitness := (Fin 5109 ⊕ Fin 73) × Fin 576

def extendedMask (i : Fin 5109) (p : PermIndex) : ℕ :=
  independentMasks.get i.val ||| 2 ^ p.val

/-- Existing coordinates are immediate. Other cases check one exact image mask. -/
def ValidExtension (i : Fin 5109) (p : PermIndex) (e : ExtensionWitness) : Prop :=
  if (independentMasks.get i.val).testBit p.val then True else
  match e with
  | (Sum.inl k, g) =>
      imageMask (literalAction g) (independentMasks.get k.val) = extendedMask i p
  | (Sum.inr k, g) =>
      let moved := imageMask (literalAction g) (circuitMasks.get k.val)
      moved &&& extendedMask i p = moved

instance (i : Fin 5109) (p : PermIndex) (e : ExtensionWitness) : Decidable (ValidExtension i p e) := by
  unfold ValidExtension
  split
  · infer_instance
  · rcases e with ⟨k,g⟩
    cases k <;> infer_instance

theorem mem_independentSupport (i : Fin 5109) (p : PermIndex) :
    p ∈ independentSupport i ↔ (independentMasks.get i.val).testBit p.val := by
  simp [independentSupport,maskSupport]

theorem mem_circuitSupport (i : Fin 73) (p : PermIndex) :
    p ∈ circuitSupport i ↔ (circuitMasks.get i.val).testBit p.val := by
  simp [circuitSupport,maskSupport]

theorem maskSupport_extendedMask (i : Fin 5109) (p : PermIndex) :
    maskSupport (extendedMask i p) = insert p (independentSupport i) :=
  maskSupport_insertBit _ _
end FourRow.Census
