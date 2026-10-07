module

public import FourRow.CensusTableData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource06 (i : Fin 8) : Fin 73 := ⟨48+i.val, by omega⟩
theorem primitive_checked_06 : ∀ i : Fin 8, ValidPrimitive (primitiveSource06 i) := by decide +kernel
end FourRow.Census
