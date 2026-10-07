module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Primitive08

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource09 (i : Fin 1) : Fin 73 := ⟨72+i.val, by omega⟩
theorem primitive_checked_09 : ∀ i : Fin 1, ValidPrimitive (primitiveSource09 i) := by decide +kernel
end FourRow.Census
