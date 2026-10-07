module

public import FourRow.GramData

@[expose] public section
namespace FourRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The ordered defect sum contains each of the 72 unordered squares four times. -/
theorem defect_explicit (a : Cell → ℝ) :
    defect a / 4000 = (1/1000 : ℝ) * ((a 0 * a 1 - a 4 * a 5) ^ 2 + (a 0 * a 4 - a 1 * a 5) ^ 2 + (a 0 * a 2 - a 4 * a 6) ^ 2 + (a 0 * a 4 - a 2 * a 6) ^ 2 + (a 0 * a 3 - a 4 * a 7) ^ 2 + (a 0 * a 4 - a 3 * a 7) ^ 2 + (a 1 * a 2 - a 5 * a 6) ^ 2 + (a 1 * a 5 - a 2 * a 6) ^ 2 + (a 1 * a 3 - a 5 * a 7) ^ 2 + (a 1 * a 5 - a 3 * a 7) ^ 2 + (a 2 * a 3 - a 6 * a 7) ^ 2 + (a 2 * a 6 - a 3 * a 7) ^ 2 + (a 0 * a 1 - a 8 * a 9) ^ 2 + (a 0 * a 8 - a 1 * a 9) ^ 2 + (a 0 * a 2 - a 8 * a 10) ^ 2 + (a 0 * a 8 - a 2 * a 10) ^ 2 + (a 0 * a 3 - a 8 * a 11) ^ 2 + (a 0 * a 8 - a 3 * a 11) ^ 2 + (a 1 * a 2 - a 9 * a 10) ^ 2 + (a 1 * a 9 - a 2 * a 10) ^ 2 + (a 1 * a 3 - a 9 * a 11) ^ 2 + (a 1 * a 9 - a 3 * a 11) ^ 2 + (a 2 * a 3 - a 10 * a 11) ^ 2 + (a 2 * a 10 - a 3 * a 11) ^ 2 + (a 0 * a 1 - a 12 * a 13) ^ 2 + (a 0 * a 12 - a 1 * a 13) ^ 2 + (a 0 * a 2 - a 12 * a 14) ^ 2 + (a 0 * a 12 - a 2 * a 14) ^ 2 + (a 0 * a 3 - a 12 * a 15) ^ 2 + (a 0 * a 12 - a 3 * a 15) ^ 2 + (a 1 * a 2 - a 13 * a 14) ^ 2 + (a 1 * a 13 - a 2 * a 14) ^ 2 + (a 1 * a 3 - a 13 * a 15) ^ 2 + (a 1 * a 13 - a 3 * a 15) ^ 2 + (a 2 * a 3 - a 14 * a 15) ^ 2 + (a 2 * a 14 - a 3 * a 15) ^ 2 + (a 4 * a 5 - a 8 * a 9) ^ 2 + (a 4 * a 8 - a 5 * a 9) ^ 2 + (a 4 * a 6 - a 8 * a 10) ^ 2 + (a 4 * a 8 - a 6 * a 10) ^ 2 + (a 4 * a 7 - a 8 * a 11) ^ 2 + (a 4 * a 8 - a 7 * a 11) ^ 2 + (a 5 * a 6 - a 9 * a 10) ^ 2 + (a 5 * a 9 - a 6 * a 10) ^ 2 + (a 5 * a 7 - a 9 * a 11) ^ 2 + (a 5 * a 9 - a 7 * a 11) ^ 2 + (a 6 * a 7 - a 10 * a 11) ^ 2 + (a 6 * a 10 - a 7 * a 11) ^ 2 + (a 4 * a 5 - a 12 * a 13) ^ 2 + (a 4 * a 12 - a 5 * a 13) ^ 2 + (a 4 * a 6 - a 12 * a 14) ^ 2 + (a 4 * a 12 - a 6 * a 14) ^ 2 + (a 4 * a 7 - a 12 * a 15) ^ 2 + (a 4 * a 12 - a 7 * a 15) ^ 2 + (a 5 * a 6 - a 13 * a 14) ^ 2 + (a 5 * a 13 - a 6 * a 14) ^ 2 + (a 5 * a 7 - a 13 * a 15) ^ 2 + (a 5 * a 13 - a 7 * a 15) ^ 2 + (a 6 * a 7 - a 14 * a 15) ^ 2 + (a 6 * a 14 - a 7 * a 15) ^ 2 + (a 8 * a 9 - a 12 * a 13) ^ 2 + (a 8 * a 12 - a 9 * a 13) ^ 2 + (a 8 * a 10 - a 12 * a 14) ^ 2 + (a 8 * a 12 - a 10 * a 14) ^ 2 + (a 8 * a 11 - a 12 * a 15) ^ 2 + (a 8 * a 12 - a 11 * a 15) ^ 2 + (a 9 * a 10 - a 13 * a 14) ^ 2 + (a 9 * a 13 - a 10 * a 14) ^ 2 + (a 9 * a 11 - a 13 * a 15) ^ 2 + (a 9 * a 13 - a 11 * a 15) ^ 2 + (a 10 * a 11 - a 14 * a 15) ^ 2 + (a 10 * a 14 - a 11 * a 15) ^ 2) := by
  norm_num [defect, cell, Fin.sum_univ_succ]
  ring

/-- The fixed lexicographic permutation sum, expanded once for arbitrary coefficients. -/
theorem weighted_sum_explicit (w : PermIndex → ℚ) (a : Cell → ℝ) :
    (∑ p, (w p : ℝ) * monomial a p) = (w 0 : ℝ) * (a 0 * a 5 * a 10 * a 15) + (w 1 : ℝ) * (a 0 * a 5 * a 11 * a 14) + (w 2 : ℝ) * (a 0 * a 6 * a 9 * a 15) + (w 3 : ℝ) * (a 0 * a 6 * a 11 * a 13) + (w 4 : ℝ) * (a 0 * a 7 * a 9 * a 14) + (w 5 : ℝ) * (a 0 * a 7 * a 10 * a 13) + (w 6 : ℝ) * (a 1 * a 4 * a 10 * a 15) + (w 7 : ℝ) * (a 1 * a 4 * a 11 * a 14) + (w 8 : ℝ) * (a 1 * a 6 * a 8 * a 15) + (w 9 : ℝ) * (a 1 * a 6 * a 11 * a 12) + (w 10 : ℝ) * (a 1 * a 7 * a 8 * a 14) + (w 11 : ℝ) * (a 1 * a 7 * a 10 * a 12) + (w 12 : ℝ) * (a 2 * a 4 * a 9 * a 15) + (w 13 : ℝ) * (a 2 * a 4 * a 11 * a 13) + (w 14 : ℝ) * (a 2 * a 5 * a 8 * a 15) + (w 15 : ℝ) * (a 2 * a 5 * a 11 * a 12) + (w 16 : ℝ) * (a 2 * a 7 * a 8 * a 13) + (w 17 : ℝ) * (a 2 * a 7 * a 9 * a 12) + (w 18 : ℝ) * (a 3 * a 4 * a 9 * a 14) + (w 19 : ℝ) * (a 3 * a 4 * a 10 * a 13) + (w 20 : ℝ) * (a 3 * a 5 * a 8 * a 14) + (w 21 : ℝ) * (a 3 * a 5 * a 10 * a 12) + (w 22 : ℝ) * (a 3 * a 6 * a 8 * a 13) + (w 23 : ℝ) * (a 3 * a 6 * a 9 * a 12) := by
  norm_num [monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp only [← add_assoc, ← mul_assoc]

/-- The fixed sum of sixteen cell squares. -/
theorem square_sum_explicit (a : Cell → ℝ) :
    (∑ j, a j ^ 2) = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 + a 9 ^ 2 + a 10 ^ 2 + a 11 ^ 2 + a 12 ^ 2 + a 13 ^ 2 + a 14 ^ 2 + a 15 ^ 2 := by
  simp [Fin.sum_univ_succ, ← add_assoc]

end FourRow
