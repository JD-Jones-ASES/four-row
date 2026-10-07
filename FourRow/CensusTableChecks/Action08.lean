module

public import FourRow.CensusTableData

import FourRow.CensusTableChecks.Action07

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem action_checked_08 : ∀ c : Fin 24, ValidAction (actionPair 8 c) := by decide +kernel
end FourRow.Census
