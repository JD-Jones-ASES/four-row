import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem action_checked_12 : ∀ c : Fin 24, ValidAction (actionPair 12 c) := by decide +kernel
end FourRow.Census
