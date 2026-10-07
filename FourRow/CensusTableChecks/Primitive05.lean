module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Primitive04

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource05 (i : Fin 8) : Fin 73 := ⟨40+i.val, by omega⟩
theorem primitive_checked_05 : ∀ i : Fin 8, ValidPrimitive (primitiveSource05 i) := by decide +kernel
end FourRow.Census
