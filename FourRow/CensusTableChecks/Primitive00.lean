module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Action23

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource00 (i : Fin 8) : Fin 73 := ⟨0+i.val, by omega⟩
theorem primitive_checked_00 : ∀ i : Fin 8, ValidPrimitive (primitiveSource00 i) := by decide +kernel
end FourRow.Census
