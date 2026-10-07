module

public import FourRow.CensusTableData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem action_checked_11 : ∀ c : Fin 24, ValidAction (actionPair 11 c) := by decide +kernel
end FourRow.Census
