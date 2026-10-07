import FourRow.CensusTableData
import FourRow.GramData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
def primitiveL1 : Fin 73 → ℤ := ![4,6,6,6,8,8,8,8,8,8,10,8,8,8,8,10,10,10,10,12,10,10,12,10,12,10,10,14,12,12,14,10,10,10,12,12,12,14,12,12,12,14,14,14,14,14,14,12,16,16,12,18,12,12,12,12,12,14,16,12,14,14,14,14,16,16,20,18,14,16,18,16,16]
def positiveGram : Fin 73 → Fin 131 := ![0,1,2,3,4,6,8,10,11,12,13,14,16,17,18,19,21,23,25,27,29,31,33,35,36,38,39,41,42,44,46,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109,111,113,115,117,119,121,123,125,127,129]
def positiveRelabel : Fin 73 → Fin 576 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def negativeGram : Fin 73 → Fin 131 := ![0,1,2,3,5,7,9,10,11,12,13,15,16,17,18,20,22,24,26,28,30,32,34,35,37,38,40,41,43,45,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130]
def negativeRelabel : Fin 73 → Fin 576 := ![1,1,1,50,0,0,0,24,2,2,30,0,24,2,25,0,0,0,0,0,0,0,0,30,0,30,0,30,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem primitiveL1_eq : ∀ k : Fin 73,
    ∑ p : PermIndex, |primitive k p| = primitiveL1 k := by decide +kernel

theorem primitiveL1_pos : ∀ k : Fin 73, 0 < primitiveL1 k := by decide +kernel

theorem positive_orientation_rat : ∀ k : Fin 73, ∀ p : PermIndex,
    (2 : ℚ) * (primitive k (literalAction (positiveRelabel k) p) : ℚ) =
      (primitiveL1 k : ℚ) * representative (positiveGram k) p := by decide +kernel

theorem negative_orientation_rat : ∀ k : Fin 73, ∀ p : PermIndex,
    (-2 : ℚ) * (primitive k (literalAction (negativeRelabel k) p) : ℚ) =
      (primitiveL1 k : ℚ) * representative (negativeGram k) p := by decide +kernel
end FourRow.Census
