import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource01 (i : Fin 8) : Fin 73 := ⟨8+i.val, by omega⟩
theorem primitive_checked_01 : ∀ i : Fin 8, ValidPrimitive (primitiveSource01 i) := by decide +kernel
end FourRow.Census
