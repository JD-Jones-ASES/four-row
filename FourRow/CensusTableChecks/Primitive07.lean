module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Primitive06

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource07 (i : Fin 8) : Fin 73 := ⟨56+i.val, by omega⟩
theorem primitive_checked_07 : ∀ i : Fin 8, ValidPrimitive (primitiveSource07 i) := by decide +kernel
end FourRow.Census
