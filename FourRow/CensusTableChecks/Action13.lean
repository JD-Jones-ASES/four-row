import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem action_checked_13 : ∀ c : Fin 24, ValidAction (actionPair 13 c) := by decide +kernel
end FourRow.Census
