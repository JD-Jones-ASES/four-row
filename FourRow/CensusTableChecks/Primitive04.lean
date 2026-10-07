import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveSource04 (i : Fin 8) : Fin 73 := ⟨32+i.val, by omega⟩
theorem primitive_checked_04 : ∀ i : Fin 8, ValidPrimitive (primitiveSource04 i) := by decide +kernel
end FourRow.Census
