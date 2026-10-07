import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource03 (i : Fin 8) : Fin 73 := ⟨24+i.val, by omega⟩
theorem primitive_checked_03 : ∀ i : Fin 8, ValidPrimitive (primitiveSource03 i) := by decide +kernel
end FourRow.Census
