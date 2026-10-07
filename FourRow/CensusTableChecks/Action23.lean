import FourRow.CensusTableData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem action_checked_23 : ∀ c : Fin 24, ValidAction (actionPair 23 c) := by decide +kernel
end FourRow.Census
