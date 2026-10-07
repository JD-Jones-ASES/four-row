import FourRow.CensusTableData
import Mathlib.Algebra.BigOperators.Ring.Finset
import FourRow.CensusTableChecks.Action00
import FourRow.CensusTableChecks.Action01
import FourRow.CensusTableChecks.Action02
import FourRow.CensusTableChecks.Action03
import FourRow.CensusTableChecks.Action04
import FourRow.CensusTableChecks.Action05
import FourRow.CensusTableChecks.Action06
import FourRow.CensusTableChecks.Action07
import FourRow.CensusTableChecks.Action08
import FourRow.CensusTableChecks.Action09
import FourRow.CensusTableChecks.Action10
import FourRow.CensusTableChecks.Action11
import FourRow.CensusTableChecks.Action12
import FourRow.CensusTableChecks.Action13
import FourRow.CensusTableChecks.Action14
import FourRow.CensusTableChecks.Action15
import FourRow.CensusTableChecks.Action16
import FourRow.CensusTableChecks.Action17
import FourRow.CensusTableChecks.Action18
import FourRow.CensusTableChecks.Action19
import FourRow.CensusTableChecks.Action20
import FourRow.CensusTableChecks.Action21
import FourRow.CensusTableChecks.Action22
import FourRow.CensusTableChecks.Action23
import FourRow.CensusTableChecks.Primitive00
import FourRow.CensusTableChecks.Primitive01
import FourRow.CensusTableChecks.Primitive02
import FourRow.CensusTableChecks.Primitive03
import FourRow.CensusTableChecks.Primitive04
import FourRow.CensusTableChecks.Primitive05
import FourRow.CensusTableChecks.Primitive06
import FourRow.CensusTableChecks.Primitive07
import FourRow.CensusTableChecks.Primitive08
import FourRow.CensusTableChecks.Primitive09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
theorem actionPair_valid (r c : Fin 24) : ValidAction (actionPair r c) := by
  fin_cases r
  · exact action_checked_00 c
  · exact action_checked_01 c
  · exact action_checked_02 c
  · exact action_checked_03 c
  · exact action_checked_04 c
  · exact action_checked_05 c
  · exact action_checked_06 c
  · exact action_checked_07 c
  · exact action_checked_08 c
  · exact action_checked_09 c
  · exact action_checked_10 c
  · exact action_checked_11 c
  · exact action_checked_12 c
  · exact action_checked_13 c
  · exact action_checked_14 c
  · exact action_checked_15 c
  · exact action_checked_16 c
  · exact action_checked_17 c
  · exact action_checked_18 c
  · exact action_checked_19 c
  · exact action_checked_20 c
  · exact action_checked_21 c
  · exact action_checked_22 c
  · exact action_checked_23 c

theorem all_action_valid (g : Fin 576) : ValidAction g := by
  let r : Fin 24 := ⟨g.val / 24, by omega⟩
  let c : Fin 24 := ⟨g.val % 24, by omega⟩
  have hg : actionPair r c = g := by
    apply Fin.ext
    simp only [actionPair, r, c]
    omega
  rw [← hg]
  exact actionPair_valid r c

theorem literalAction_permutation (g : Fin 576) (p : PermIndex) (i : Row) :
  permutation (literalAction g p) i =
    permutation ⟨g.val % 24, by omega⟩ (permutation p
      (permutation (inverseIndex ⟨g.val / 24, by omega⟩) i)) := all_action_valid g p i

theorem literalAction_eq (g : Fin 576) (p : PermIndex) :
  literalAction g p = action (relabel g) p := by
  apply permEquiv_bijective.1
  apply Equiv.ext
  intro i
  change permutation (literalAction g p) i = permutation (action (relabel g) p) i
  have h := congrArg (fun σ : Perm4 => σ i)
    (show lexEquiv (action (relabel g) p) = (relabel g).2 * lexEquiv p * (relabel g).1⁻¹ by
      simp [action,Equiv.trans_apply])
  exact (literalAction_permutation g p i).trans h.symm

theorem all_primitives_valid (k : Fin 73) : ValidPrimitive k := by
  fin_cases k
  · exact primitive_checked_00 0
  · exact primitive_checked_00 1
  · exact primitive_checked_00 2
  · exact primitive_checked_00 3
  · exact primitive_checked_00 4
  · exact primitive_checked_00 5
  · exact primitive_checked_00 6
  · exact primitive_checked_00 7
  · exact primitive_checked_01 0
  · exact primitive_checked_01 1
  · exact primitive_checked_01 2
  · exact primitive_checked_01 3
  · exact primitive_checked_01 4
  · exact primitive_checked_01 5
  · exact primitive_checked_01 6
  · exact primitive_checked_01 7
  · exact primitive_checked_02 0
  · exact primitive_checked_02 1
  · exact primitive_checked_02 2
  · exact primitive_checked_02 3
  · exact primitive_checked_02 4
  · exact primitive_checked_02 5
  · exact primitive_checked_02 6
  · exact primitive_checked_02 7
  · exact primitive_checked_03 0
  · exact primitive_checked_03 1
  · exact primitive_checked_03 2
  · exact primitive_checked_03 3
  · exact primitive_checked_03 4
  · exact primitive_checked_03 5
  · exact primitive_checked_03 6
  · exact primitive_checked_03 7
  · exact primitive_checked_04 0
  · exact primitive_checked_04 1
  · exact primitive_checked_04 2
  · exact primitive_checked_04 3
  · exact primitive_checked_04 4
  · exact primitive_checked_04 5
  · exact primitive_checked_04 6
  · exact primitive_checked_04 7
  · exact primitive_checked_05 0
  · exact primitive_checked_05 1
  · exact primitive_checked_05 2
  · exact primitive_checked_05 3
  · exact primitive_checked_05 4
  · exact primitive_checked_05 5
  · exact primitive_checked_05 6
  · exact primitive_checked_05 7
  · exact primitive_checked_06 0
  · exact primitive_checked_06 1
  · exact primitive_checked_06 2
  · exact primitive_checked_06 3
  · exact primitive_checked_06 4
  · exact primitive_checked_06 5
  · exact primitive_checked_06 6
  · exact primitive_checked_06 7
  · exact primitive_checked_07 0
  · exact primitive_checked_07 1
  · exact primitive_checked_07 2
  · exact primitive_checked_07 3
  · exact primitive_checked_07 4
  · exact primitive_checked_07 5
  · exact primitive_checked_07 6
  · exact primitive_checked_07 7
  · exact primitive_checked_08 0
  · exact primitive_checked_08 1
  · exact primitive_checked_08 2
  · exact primitive_checked_08 3
  · exact primitive_checked_08 4
  · exact primitive_checked_08 5
  · exact primitive_checked_08 6
  · exact primitive_checked_08 7
  · exact primitive_checked_09 0

theorem primitive_support (i : Fin 73) (p : PermIndex) :
    p ∈ circuitSupport i ↔ primitive i p ≠ 0 := (all_primitives_valid i).1 p

theorem primitive_nonzero (i : Fin 73) : ∃ p, primitive i p ≠ 0 :=
  (all_primitives_valid i).2.1

theorem primitive_kernel_int (k : Fin 73) (i j : Row) :
    ∑ p, incidence i j p * primitive k p = 0 := (all_primitives_valid k).2.2 i j

theorem primitive_kernel (k : Fin 73) : Kernel (fun p => (primitive k p : ℝ)) := by
  intro i j
  change (∑ p : PermIndex, (incidence i j p : ℝ) * (primitive k p : ℝ)) = 0
  exact_mod_cast primitive_kernel_int k i j

end FourRow.Census
