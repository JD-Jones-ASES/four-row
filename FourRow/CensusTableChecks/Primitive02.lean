module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Primitive01

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource02 (i : Fin 8) : Fin 73 := ⟨16+i.val, by omega⟩
theorem primitive_checked_02 : ∀ i : Fin 8, ValidPrimitive (primitiveSource02 i) := by decide +kernel
end FourRow.Census
