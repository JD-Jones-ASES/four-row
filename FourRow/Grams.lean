module

public import FourRow.GramBridge
public import FourRow.Grams.G000
public import FourRow.Grams.G001
public import FourRow.Grams.G002
public import FourRow.Grams.G003
public import FourRow.Grams.G004
public import FourRow.Grams.G005
public import FourRow.Grams.G006
public import FourRow.Grams.G007
public import FourRow.Grams.G008
public import FourRow.Grams.G009
public import FourRow.Grams.G010
public import FourRow.Grams.G011
public import FourRow.Grams.G012
public import FourRow.Grams.G013
public import FourRow.Grams.G014
public import FourRow.Grams.G015
public import FourRow.Grams.G016
public import FourRow.Grams.G017
public import FourRow.Grams.G018
public import FourRow.Grams.G019
public import FourRow.Grams.G020
public import FourRow.Grams.G021
public import FourRow.Grams.G022
public import FourRow.Grams.G023
public import FourRow.Grams.G024
public import FourRow.Grams.G025
public import FourRow.Grams.G026
public import FourRow.Grams.G027
public import FourRow.Grams.G028
public import FourRow.Grams.G029
public import FourRow.Grams.G030
public import FourRow.Grams.G031
public import FourRow.Grams.G032
public import FourRow.Grams.G033
public import FourRow.Grams.G034
public import FourRow.Grams.G035
public import FourRow.Grams.G036
public import FourRow.Grams.G037
public import FourRow.Grams.G038
public import FourRow.Grams.G039
public import FourRow.Grams.G040
public import FourRow.Grams.G041
public import FourRow.Grams.G042
public import FourRow.Grams.G043
public import FourRow.Grams.G044
public import FourRow.Grams.G045
public import FourRow.Grams.G046
public import FourRow.Grams.G047
public import FourRow.Grams.G048
public import FourRow.Grams.G049
public import FourRow.Grams.G050
public import FourRow.Grams.G051
public import FourRow.Grams.G052
public import FourRow.Grams.G053
public import FourRow.Grams.G054
public import FourRow.Grams.G055
public import FourRow.Grams.G056
public import FourRow.Grams.G057
public import FourRow.Grams.G058
public import FourRow.Grams.G059
public import FourRow.Grams.G060
public import FourRow.Grams.G061
public import FourRow.Grams.G062
public import FourRow.Grams.G063
public import FourRow.Grams.G064
public import FourRow.Grams.G065
public import FourRow.Grams.G066
public import FourRow.Grams.G067
public import FourRow.Grams.G068
public import FourRow.Grams.G069
public import FourRow.Grams.G070
public import FourRow.Grams.G071
public import FourRow.Grams.G072
public import FourRow.Grams.G073
public import FourRow.Grams.G074
public import FourRow.Grams.G075
public import FourRow.Grams.G076
public import FourRow.Grams.G077
public import FourRow.Grams.G078
public import FourRow.Grams.G079
public import FourRow.Grams.G080
public import FourRow.Grams.G081
public import FourRow.Grams.G082
public import FourRow.Grams.G083
public import FourRow.Grams.G084
public import FourRow.Grams.G085
public import FourRow.Grams.G086
public import FourRow.Grams.G087
public import FourRow.Grams.G088
public import FourRow.Grams.G089
public import FourRow.Grams.G090
public import FourRow.Grams.G091
public import FourRow.Grams.G092
public import FourRow.Grams.G093
public import FourRow.Grams.G094
public import FourRow.Grams.G095
public import FourRow.Grams.G096
public import FourRow.Grams.G097
public import FourRow.Grams.G098
public import FourRow.Grams.G099
public import FourRow.Grams.G100
public import FourRow.Grams.G101
public import FourRow.Grams.G102
public import FourRow.Grams.G103
public import FourRow.Grams.G104
public import FourRow.Grams.G105
public import FourRow.Grams.G106
public import FourRow.Grams.G107
public import FourRow.Grams.G108
public import FourRow.Grams.G109
public import FourRow.Grams.G110
public import FourRow.Grams.G111
public import FourRow.Grams.G112
public import FourRow.Grams.G113
public import FourRow.Grams.G114
public import FourRow.Grams.G115
public import FourRow.Grams.G116
public import FourRow.Grams.G117
public import FourRow.Grams.G118
public import FourRow.Grams.G119
public import FourRow.Grams.G120
public import FourRow.Grams.G121
public import FourRow.Grams.G122
public import FourRow.Grams.G123
public import FourRow.Grams.G124
public import FourRow.Grams.G125
public import FourRow.Grams.G126
public import FourRow.Grams.G127
public import FourRow.Grams.G128
public import FourRow.Grams.G129
public import FourRow.Grams.G130

@[expose] public section

namespace FourRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every supplied representative satisfies the full real quartic inequality.
All 131 identities are checked by Lean's polynomial normalization and positivity;
the source-generating Python script contributes no axiom to this theorem. -/
theorem gram_strong (k : Fin 131) (a : Cell → ℝ) :
    0 ≤ (3/32 : ℝ) * (∑ j, a j ^ 2) ^ 2 -
      (∑ p, (weights k p : ℝ) * monomial a p) - defect a / 4000 := by
  rw [defect_explicit, square_sum_explicit, weighted_sum_explicit]
  fin_cases k
  · have hw : weights 0 = ![3/2, 1/2, 1, 1, 1, 1, 1/2, 3/2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram000 a
  · have hw : weights 1 = ![4/3, 2/3, 2/3, 4/3, 4/3, 2/3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram001 a
  · have hw : weights 2 = ![1, 1, 4/3, 2/3, 2/3, 4/3, 2/3, 4/3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram002 a
  · have hw : weights 3 = ![1, 1, 1, 4/3, 2/3, 1, 1, 1, 2/3, 1, 4/3, 1, 4/3, 2/3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram003 a
  · have hw : weights 4 = ![3/2, 3/4, 1, 1, 1, 3/4, 3/4, 1, 1, 1, 5/4, 1, 1, 5/4, 3/4, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram004 a
  · have hw : weights 5 = ![1/2, 5/4, 1, 1, 1, 5/4, 5/4, 1, 1, 1, 3/4, 1, 1, 3/4, 5/4, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram005 a
  · have hw : weights 6 = ![5/4, 3/4, 5/4, 1, 1, 3/4, 1, 1, 3/4, 1, 5/4, 1, 3/4, 5/4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram006 a
  · have hw : weights 7 = ![3/4, 5/4, 3/4, 1, 1, 5/4, 1, 1, 5/4, 1, 3/4, 1, 5/4, 3/4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram007 a
  · have hw : weights 8 = ![1, 1, 5/4, 1, 1, 3/4, 5/4, 3/4, 3/4, 1, 5/4, 1, 3/4, 5/4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram008 a
  · have hw : weights 9 = ![1, 1, 3/4, 1, 1, 5/4, 3/4, 5/4, 5/4, 1, 3/4, 1, 5/4, 3/4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram009 a
  · have hw : weights 10 = ![1, 1, 1, 1, 5/4, 3/4, 1, 1, 5/4, 3/4, 3/4, 5/4, 3/4, 5/4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram010 a
  · have hw : weights 11 = ![1, 5/4, 1, 3/4, 3/4, 5/4, 3/4, 1, 5/4, 1, 1, 1, 5/4, 1, 3/4, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram011 a
  · have hw : weights 12 = ![5/4, 1, 3/4, 1, 5/4, 3/4, 1, 3/4, 5/4, 1, 1, 1, 1, 5/4, 3/4, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram012 a
  · have hw : weights 13 = ![1, 6/5, 1, 3/5, 1, 6/5, 4/5, 1, 7/5, 1, 4/5, 1, 1, 6/5, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram013 a
  · have hw : weights 14 = ![1, 1, 5/4, 1, 1, 3/4, 1, 1, 1, 3/4, 5/4, 1, 1, 1, 3/4, 5/4, 1, 1, 3/4, 5/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram014 a
  · have hw : weights 15 = ![1, 1, 3/4, 1, 1, 5/4, 1, 1, 1, 5/4, 3/4, 1, 1, 1, 5/4, 3/4, 1, 1, 5/4, 3/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram015 a
  · have hw : weights 16 = ![1, 1, 5/4, 3/4, 1, 1, 1, 1, 1, 1, 5/4, 3/4, 1, 1, 3/4, 5/4, 1, 1, 3/4, 5/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram016 a
  · have hw : weights 17 = ![5/4, 1, 3/4, 1, 1, 1, 1, 1, 1, 5/4, 3/4, 1, 1, 1, 1, 3/4, 5/4, 1, 5/4, 3/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram017 a
  · have hw : weights 18 = ![1, 1, 1, 5/4, 3/4, 1, 1, 1, 3/4, 1, 1, 5/4, 5/4, 1, 1, 3/4, 1, 1, 1, 3/4, 5/4, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram018 a
  · have hw : weights 19 = ![6/5, 3/5, 1, 6/5, 6/5, 4/5, 1, 6/5, 4/5, 1, 1, 1, 4/5, 1, 6/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram019 a
  · have hw : weights 20 = ![4/5, 7/5, 1, 4/5, 4/5, 6/5, 1, 4/5, 6/5, 1, 1, 1, 6/5, 1, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram020 a
  · have hw : weights 21 = ![6/5, 1, 3/5, 6/5, 6/5, 4/5, 1, 4/5, 6/5, 1, 1, 1, 6/5, 1, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram021 a
  · have hw : weights 22 = ![4/5, 1, 7/5, 4/5, 4/5, 6/5, 1, 6/5, 4/5, 1, 1, 1, 4/5, 1, 6/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram022 a
  · have hw : weights 23 = ![1, 6/5, 4/5, 6/5, 1, 4/5, 6/5, 3/5, 1, 1, 6/5, 1, 6/5, 1, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram023 a
  · have hw : weights 24 = ![1, 4/5, 6/5, 4/5, 1, 6/5, 4/5, 7/5, 1, 1, 4/5, 1, 4/5, 1, 6/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram024 a
  · have hw : weights 25 = ![1, 6/5, 4/5, 1, 6/5, 4/5, 6/5, 3/5, 6/5, 1, 1, 1, 1, 6/5, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram025 a
  · have hw : weights 26 = ![1, 4/5, 6/5, 1, 4/5, 6/5, 4/5, 7/5, 4/5, 1, 1, 1, 1, 4/5, 6/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram026 a
  · have hw : weights 27 = ![1, 7/6, 4/3, 2/3, 2/3, 7/6, 5/6, 1, 1, 1, 7/6, 1, 1, 7/6, 5/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram027 a
  · have hw : weights 28 = ![1, 5/6, 2/3, 4/3, 4/3, 5/6, 7/6, 1, 1, 1, 5/6, 1, 1, 5/6, 7/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram028 a
  · have hw : weights 29 = ![7/5, 4/5, 4/5, 1, 1, 1, 1, 1, 1, 6/5, 1, 4/5, 1, 1, 4/5, 1, 6/5, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram029 a
  · have hw : weights 30 = ![3/5, 6/5, 6/5, 1, 1, 1, 1, 1, 1, 4/5, 1, 6/5, 1, 1, 6/5, 1, 4/5, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram030 a
  · have hw : weights 31 = ![1, 6/5, 6/5, 1, 1, 3/5, 1, 1, 1, 4/5, 1, 6/5, 1, 1, 4/5, 1, 6/5, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram031 a
  · have hw : weights 32 = ![1, 4/5, 4/5, 1, 1, 7/5, 1, 1, 1, 6/5, 1, 4/5, 1, 1, 6/5, 1, 4/5, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram032 a
  · have hw : weights 33 = ![7/6, 1, 1, 7/6, 2/3, 1, 1, 1, 5/6, 1, 1, 7/6, 1, 1, 1, 5/6, 7/6, 1, 4/3, 2/3, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram033 a
  · have hw : weights 34 = ![5/6, 1, 1, 5/6, 4/3, 1, 1, 1, 7/6, 1, 1, 5/6, 1, 1, 1, 7/6, 5/6, 1, 2/3, 4/3, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram034 a
  · have hw : weights 35 = ![1, 6/5, 6/5, 4/5, 4/5, 1, 4/5, 1, 6/5, 4/5, 1, 6/5, 1, 6/5, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram035 a
  · have hw : weights 36 = ![1, 7/6, 7/6, 1, 5/6, 5/6, 5/6, 1, 7/6, 2/3, 1, 4/3, 1, 7/6, 5/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram036 a
  · have hw : weights 37 = ![1, 5/6, 5/6, 1, 7/6, 7/6, 7/6, 1, 5/6, 4/3, 1, 2/3, 1, 5/6, 7/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram037 a
  · have hw : weights 38 = ![6/5, 1, 4/5, 4/5, 6/5, 1, 1, 4/5, 6/5, 6/5, 1, 4/5, 1, 6/5, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram038 a
  · have hw : weights 39 = ![6/5, 1, 6/5, 1, 4/5, 4/5, 4/5, 1, 1, 4/5, 6/5, 6/5, 1, 6/5, 4/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram039 a
  · have hw : weights 40 = ![4/5, 1, 4/5, 1, 6/5, 6/5, 6/5, 1, 1, 6/5, 4/5, 4/5, 1, 4/5, 6/5, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram040 a
  · have hw : weights 41 = ![1, 8/7, 9/7, 1, 5/7, 6/7, 6/7, 1, 1, 5/7, 8/7, 9/7, 1, 8/7, 6/7, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram041 a
  · have hw : weights 42 = ![7/6, 1, 1, 2/3, 7/6, 1, 1, 5/6, 7/6, 7/6, 1, 5/6, 5/6, 4/3, 5/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram042 a
  · have hw : weights 43 = ![5/6, 1, 1, 4/3, 5/6, 1, 1, 7/6, 5/6, 5/6, 1, 7/6, 7/6, 2/3, 7/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram043 a
  · have hw : weights 44 = ![7/6, 1, 1, 1, 7/6, 2/3, 1, 5/6, 7/6, 5/6, 1, 7/6, 5/6, 4/3, 5/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram044 a
  · have hw : weights 45 = ![5/6, 1, 1, 1, 5/6, 4/3, 1, 7/6, 5/6, 7/6, 1, 5/6, 7/6, 2/3, 7/6, 1, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram045 a
  · have hw : weights 46 = ![1, 8/7, 5/7, 1, 1, 8/7, 6/7, 1, 1, 9/7, 6/7, 1, 9/7, 6/7, 8/7, 5/7, 1, 1, 1, 1, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram046 a
  · have hw : weights 47 = ![1, 6/5, 1, 1, 1, 4/5, 4/5, 1, 6/5, 4/5, 1, 6/5, 6/5, 1, 4/5, 1, 1, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram047 a
  · have hw : weights 48 = ![1, 4/5, 1, 1, 1, 6/5, 6/5, 1, 4/5, 6/5, 1, 4/5, 4/5, 1, 6/5, 1, 1, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram048 a
  · have hw : weights 49 = ![6/5, 1, 1, 4/5, 1, 1, 4/5, 1, 1, 6/5, 6/5, 4/5, 6/5, 1, 4/5, 1, 1, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram049 a
  · have hw : weights 50 = ![4/5, 1, 1, 6/5, 1, 1, 6/5, 1, 1, 4/5, 4/5, 6/5, 4/5, 1, 6/5, 1, 1, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram050 a
  · have hw : weights 51 = ![6/5, 4/5, 1, 1, 1, 1, 6/5, 1, 4/5, 6/5, 1, 4/5, 4/5, 1, 1, 1, 6/5, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram051 a
  · have hw : weights 52 = ![4/5, 6/5, 1, 1, 1, 1, 4/5, 1, 6/5, 4/5, 1, 6/5, 6/5, 1, 1, 1, 4/5, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram052 a
  · have hw : weights 53 = ![4/3, 2/3, 1, 1, 1, 1, 1, 7/6, 5/6, 7/6, 1, 5/6, 5/6, 1, 1, 1, 7/6, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram053 a
  · have hw : weights 54 = ![2/3, 4/3, 1, 1, 1, 1, 1, 5/6, 7/6, 5/6, 1, 7/6, 7/6, 1, 1, 1, 5/6, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram054 a
  · have hw : weights 55 = ![1, 7/6, 5/6, 1, 1, 1, 4/3, 2/3, 1, 7/6, 1, 5/6, 1, 1, 5/6, 1, 7/6, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram055 a
  · have hw : weights 56 = ![1, 5/6, 7/6, 1, 1, 1, 2/3, 4/3, 1, 5/6, 1, 7/6, 1, 1, 7/6, 1, 5/6, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram056 a
  · have hw : weights 57 = ![4/3, 5/6, 5/6, 1, 1, 1, 1, 1, 5/6, 4/3, 1, 5/6, 1, 1, 1, 5/6, 7/6, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram057 a
  · have hw : weights 58 = ![2/3, 7/6, 7/6, 1, 1, 1, 1, 1, 7/6, 2/3, 1, 7/6, 1, 1, 1, 7/6, 5/6, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram058 a
  · have hw : weights 59 = ![8/7, 1, 5/7, 8/7, 1, 1, 1, 1, 8/7, 1, 5/7, 8/7, 1, 1, 1, 6/7, 8/7, 1, 9/7, 5/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram059 a
  · have hw : weights 60 = ![6/7, 1, 9/7, 6/7, 1, 1, 1, 1, 6/7, 1, 9/7, 6/7, 1, 1, 1, 8/7, 6/7, 1, 5/7, 9/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram060 a
  · have hw : weights 61 = ![7/6, 2/3, 1, 1, 1, 7/6, 1, 7/6, 5/6, 7/6, 1, 5/6, 5/6, 1, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram061 a
  · have hw : weights 62 = ![5/6, 4/3, 1, 1, 1, 5/6, 1, 5/6, 7/6, 5/6, 1, 7/6, 7/6, 1, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram062 a
  · have hw : weights 63 = ![7/6, 1, 2/3, 1, 1, 7/6, 1, 5/6, 7/6, 7/6, 1, 5/6, 7/6, 1, 5/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram063 a
  · have hw : weights 64 = ![5/6, 1, 4/3, 1, 1, 5/6, 1, 7/6, 5/6, 5/6, 1, 7/6, 5/6, 1, 7/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram064 a
  · have hw : weights 65 = ![7/6, 1, 1, 1, 1, 5/6, 2/3, 7/6, 7/6, 5/6, 1, 7/6, 7/6, 1, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram065 a
  · have hw : weights 66 = ![5/6, 1, 1, 1, 1, 7/6, 4/3, 5/6, 5/6, 7/6, 1, 5/6, 5/6, 1, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram066 a
  · have hw : weights 67 = ![1, 8/7, 8/7, 5/7, 1, 1, 6/7, 1, 1, 8/7, 8/7, 6/7, 8/7, 1, 6/7, 1, 1, 1, 5/7, 9/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram067 a
  · have hw : weights 68 = ![1, 6/7, 6/7, 9/7, 1, 1, 8/7, 1, 1, 6/7, 6/7, 8/7, 6/7, 1, 8/7, 1, 1, 1, 9/7, 5/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram068 a
  · have hw : weights 69 = ![1, 8/7, 8/7, 1, 1, 5/7, 6/7, 1, 1, 6/7, 8/7, 8/7, 8/7, 1, 6/7, 1, 1, 1, 5/7, 9/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram069 a
  · have hw : weights 70 = ![1, 6/7, 6/7, 1, 1, 9/7, 8/7, 1, 1, 8/7, 6/7, 6/7, 6/7, 1, 8/7, 1, 1, 1, 9/7, 5/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram070 a
  · have hw : weights 71 = ![8/7, 1, 1, 6/7, 1, 1, 1, 6/7, 6/7, 9/7, 9/7, 5/7, 8/7, 1, 6/7, 1, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram071 a
  · have hw : weights 72 = ![6/7, 1, 1, 8/7, 1, 1, 1, 8/7, 8/7, 5/7, 5/7, 9/7, 6/7, 1, 8/7, 1, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram072 a
  · have hw : weights 73 = ![1, 8/7, 8/7, 1, 5/7, 1, 6/7, 1, 8/7, 5/7, 1, 9/7, 1, 8/7, 6/7, 1, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram073 a
  · have hw : weights 74 = ![1, 6/7, 6/7, 1, 9/7, 1, 8/7, 1, 6/7, 9/7, 1, 5/7, 1, 6/7, 8/7, 1, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram074 a
  · have hw : weights 75 = ![1, 8/7, 8/7, 1, 1, 5/7, 6/7, 1, 8/7, 5/7, 1, 9/7, 1, 8/7, 6/7, 1, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram075 a
  · have hw : weights 76 = ![1, 6/7, 6/7, 1, 1, 9/7, 8/7, 1, 6/7, 9/7, 1, 5/7, 1, 6/7, 8/7, 1, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram076 a
  · have hw : weights 77 = ![10/7, 5/7, 6/7, 1, 1, 1, 6/7, 1, 1, 8/7, 8/7, 6/7, 1, 8/7, 6/7, 1, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram077 a
  · have hw : weights 78 = ![4/7, 9/7, 8/7, 1, 1, 1, 8/7, 1, 1, 6/7, 6/7, 8/7, 1, 6/7, 8/7, 1, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram078 a
  · have hw : weights 79 = ![7/6, 1, 7/6, 2/3, 1, 1, 5/6, 1, 1, 7/6, 7/6, 5/6, 1, 7/6, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram079 a
  · have hw : weights 80 = ![5/6, 1, 5/6, 4/3, 1, 1, 7/6, 1, 1, 5/6, 5/6, 7/6, 1, 5/6, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram080 a
  · have hw : weights 81 = ![1, 9/8, 5/4, 5/8, 1, 1, 7/8, 1, 1, 9/8, 9/8, 7/8, 1, 9/8, 7/8, 1, 1, 1, 3/4, 5/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram081 a
  · have hw : weights 82 = ![1, 7/8, 3/4, 11/8, 1, 1, 9/8, 1, 1, 7/8, 7/8, 9/8, 1, 7/8, 9/8, 1, 1, 1, 5/4, 3/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram082 a
  · have hw : weights 83 = ![1, 9/8, 5/4, 1, 5/8, 1, 7/8, 1, 1, 3/4, 9/8, 5/4, 1, 9/8, 7/8, 1, 1, 1, 9/8, 7/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram083 a
  · have hw : weights 84 = ![1, 7/8, 3/4, 1, 11/8, 1, 9/8, 1, 1, 5/4, 7/8, 3/4, 1, 7/8, 9/8, 1, 1, 1, 7/8, 9/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram084 a
  · have hw : weights 85 = ![7/6, 1, 7/6, 1, 1, 2/3, 5/6, 1, 1, 5/6, 7/6, 7/6, 1, 7/6, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram085 a
  · have hw : weights 86 = ![5/6, 1, 5/6, 1, 1, 4/3, 7/6, 1, 1, 7/6, 5/6, 5/6, 1, 5/6, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram086 a
  · have hw : weights 87 = ![1, 10/9, 11/9, 1, 1, 2/3, 8/9, 1, 1, 7/9, 10/9, 11/9, 1, 10/9, 8/9, 1, 1, 1, 7/9, 11/9, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram087 a
  · have hw : weights 88 = ![1, 8/9, 7/9, 1, 1, 4/3, 10/9, 1, 1, 11/9, 8/9, 7/9, 1, 8/9, 10/9, 1, 1, 1, 11/9, 7/9, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram088 a
  · have hw : weights 89 = ![4/3, 5/6, 5/6, 1, 1, 1, 1, 5/6, 1, 7/6, 7/6, 5/6, 1, 7/6, 5/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram089 a
  · have hw : weights 90 = ![2/3, 7/6, 7/6, 1, 1, 1, 1, 7/6, 1, 5/6, 5/6, 7/6, 1, 5/6, 7/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram090 a
  · have hw : weights 91 = ![1, 7/6, 7/6, 2/3, 1, 1, 1, 5/6, 1, 7/6, 7/6, 5/6, 1, 7/6, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram091 a
  · have hw : weights 92 = ![1, 5/6, 5/6, 4/3, 1, 1, 1, 7/6, 1, 5/6, 5/6, 7/6, 1, 5/6, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram092 a
  · have hw : weights 93 = ![1, 7/6, 7/6, 1, 2/3, 1, 1, 5/6, 1, 5/6, 7/6, 7/6, 1, 7/6, 5/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram093 a
  · have hw : weights 94 = ![1, 5/6, 5/6, 1, 4/3, 1, 1, 7/6, 1, 7/6, 5/6, 5/6, 1, 5/6, 7/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram094 a
  · have hw : weights 95 = ![1, 7/6, 7/6, 1, 1, 2/3, 1, 5/6, 1, 5/6, 7/6, 7/6, 1, 7/6, 5/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram095 a
  · have hw : weights 96 = ![1, 5/6, 5/6, 1, 1, 4/3, 1, 7/6, 1, 7/6, 5/6, 5/6, 1, 5/6, 7/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram096 a
  · have hw : weights 97 = ![7/6, 1, 5/6, 1, 1, 1, 7/6, 2/3, 1, 7/6, 7/6, 5/6, 1, 7/6, 5/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram097 a
  · have hw : weights 98 = ![5/6, 1, 7/6, 1, 1, 1, 5/6, 4/3, 1, 5/6, 5/6, 7/6, 1, 5/6, 7/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram098 a
  · have hw : weights 99 = ![1, 8/7, 6/7, 1, 1, 1, 9/7, 4/7, 1, 8/7, 8/7, 6/7, 1, 8/7, 6/7, 1, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram099 a
  · have hw : weights 100 = ![1, 6/7, 8/7, 1, 1, 1, 5/7, 10/7, 1, 6/7, 6/7, 8/7, 1, 6/7, 8/7, 1, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram100 a
  · have hw : weights 101 = ![1, 9/8, 7/8, 1, 1, 1, 7/8, 1, 11/8, 3/4, 3/4, 5/4, 1, 9/8, 7/8, 1, 1, 1, 9/8, 7/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram101 a
  · have hw : weights 102 = ![1, 7/8, 9/8, 1, 1, 1, 9/8, 1, 5/8, 5/4, 5/4, 3/4, 1, 7/8, 9/8, 1, 1, 1, 7/8, 9/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram102 a
  · have hw : weights 103 = ![1, 7/6, 5/6, 1, 1, 1, 1, 5/6, 4/3, 5/6, 5/6, 7/6, 1, 7/6, 5/6, 1, 1, 1, 7/6, 5/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram103 a
  · have hw : weights 104 = ![1, 5/6, 7/6, 1, 1, 1, 1, 7/6, 2/3, 7/6, 7/6, 5/6, 1, 5/6, 7/6, 1, 1, 1, 5/6, 7/6, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram104 a
  · have hw : weights 105 = ![8/7, 1, 1, 8/7, 1, 5/7, 1, 6/7, 1, 6/7, 9/7, 1, 8/7, 1, 5/7, 8/7, 1, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram105 a
  · have hw : weights 106 = ![6/7, 1, 1, 6/7, 1, 9/7, 1, 8/7, 1, 8/7, 5/7, 1, 6/7, 1, 9/7, 6/7, 1, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram106 a
  · have hw : weights 107 = ![1, 8/7, 6/7, 1, 1, 1, 5/7, 1, 9/7, 6/7, 1, 8/7, 9/7, 1, 6/7, 1, 6/7, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram107 a
  · have hw : weights 108 = ![1, 6/7, 8/7, 1, 1, 1, 9/7, 1, 5/7, 8/7, 1, 6/7, 5/7, 1, 8/7, 1, 8/7, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram108 a
  · have hw : weights 109 = ![1, 8/7, 6/7, 1, 1, 1, 1, 5/7, 1, 8/7, 9/7, 6/7, 9/7, 1, 6/7, 1, 6/7, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram109 a
  · have hw : weights 110 = ![1, 6/7, 8/7, 1, 1, 1, 1, 9/7, 1, 6/7, 5/7, 8/7, 5/7, 1, 8/7, 1, 8/7, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram110 a
  · have hw : weights 111 = ![1, 8/7, 6/7, 1, 1, 1, 1, 5/7, 9/7, 6/7, 1, 8/7, 1, 9/7, 6/7, 1, 6/7, 1, 8/7, 6/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram111 a
  · have hw : weights 112 = ![1, 6/7, 8/7, 1, 1, 1, 1, 9/7, 5/7, 8/7, 1, 6/7, 1, 5/7, 8/7, 1, 8/7, 1, 6/7, 8/7, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram112 a
  · have hw : weights 113 = ![1, 9/8, 7/8, 1, 1, 1, 5/4, 1, 1, 9/8, 3/4, 7/8, 1, 3/4, 7/8, 1, 11/8, 1, 9/8, 7/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram113 a
  · have hw : weights 114 = ![1, 7/8, 9/8, 1, 1, 1, 3/4, 1, 1, 7/8, 5/4, 9/8, 1, 5/4, 9/8, 1, 5/8, 1, 7/8, 9/8, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram114 a
  · have hw : weights 115 = ![9/8, 3/4, 1, 9/8, 1, 1, 5/4, 1, 7/8, 1, 1, 7/8, 3/4, 1, 1, 9/8, 9/8, 1, 5/4, 3/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram115 a
  · have hw : weights 116 = ![7/8, 5/4, 1, 7/8, 1, 1, 3/4, 1, 9/8, 1, 1, 9/8, 5/4, 1, 1, 7/8, 7/8, 1, 3/4, 5/4, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram116 a
  · have hw : weights 117 = ![13/10, 3/5, 1, 11/10, 1, 1, 1, 6/5, 9/10, 1, 1, 9/10, 4/5, 1, 1, 11/10, 11/10, 1, 6/5, 4/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram117 a
  · have hw : weights 118 = ![7/10, 7/5, 1, 9/10, 1, 1, 1, 4/5, 11/10, 1, 1, 11/10, 6/5, 1, 1, 9/10, 9/10, 1, 4/5, 6/5, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram118 a
  · have hw : weights 119 = ![10/9, 1, 1, 8/9, 1, 1, 5/9, 11/9, 10/9, 1, 1, 10/9, 11/9, 1, 1, 8/9, 8/9, 1, 7/9, 11/9, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram119 a
  · have hw : weights 120 = ![8/9, 1, 1, 10/9, 1, 1, 13/9, 7/9, 8/9, 1, 1, 8/9, 7/9, 1, 1, 10/9, 10/9, 1, 11/9, 7/9, 1, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram120 a
  · have hw : weights 121 = ![1, 1, 8/7, 5/7, 8/7, 1, 8/7, 1, 1, 8/7, 1, 5/7, 5/7, 1, 1, 8/7, 8/7, 1, 1, 8/7, 6/7, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram121 a
  · have hw : weights 122 = ![1, 1, 6/7, 9/7, 6/7, 1, 6/7, 1, 1, 6/7, 1, 9/7, 9/7, 1, 1, 6/7, 6/7, 1, 1, 6/7, 8/7, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram122 a
  · have hw : weights 123 = ![9/8, 5/8, 9/8, 1, 1, 9/8, 1, 9/8, 3/4, 9/8, 1, 1, 1, 9/8, 1, 1, 1, 7/8, 1, 3/4, 5/4, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram123 a
  · have hw : weights 124 = ![7/8, 11/8, 7/8, 1, 1, 7/8, 1, 7/8, 5/4, 7/8, 1, 1, 1, 7/8, 1, 1, 1, 9/8, 1, 5/4, 3/4, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram124 a
  · have hw : weights 125 = ![10/9, 1, 7/9, 4/3, 1, 7/9, 1, 10/9, 10/9, 7/9, 1, 1, 1, 7/9, 1, 1, 1, 11/9, 1, 10/9, 8/9, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram125 a
  · have hw : weights 126 = ![8/9, 1, 11/9, 2/3, 1, 11/9, 1, 8/9, 8/9, 11/9, 1, 1, 1, 11/9, 1, 1, 1, 7/9, 1, 8/9, 10/9, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram126 a
  · have hw : weights 127 = ![9/8, 1, 3/4, 1, 11/8, 3/4, 1, 3/4, 9/8, 9/8, 1, 1, 1, 9/8, 1, 1, 1, 7/8, 1, 9/8, 7/8, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram127 a
  · have hw : weights 128 = ![7/8, 1, 5/4, 1, 5/8, 5/4, 1, 5/4, 7/8, 7/8, 1, 1, 1, 7/8, 1, 1, 1, 9/8, 1, 7/8, 9/8, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram128 a
  · have hw : weights 129 = ![1, 9/8, 9/8, 3/4, 1, 1, 1, 1, 1, 9/8, 9/8, 3/4, 3/4, 1, 9/8, 1, 1, 9/8, 1, 5/4, 3/4, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram129 a
  · have hw : weights 130 = ![1, 7/8, 7/8, 5/4, 1, 1, 1, 1, 1, 7/8, 7/8, 5/4, 5/4, 1, 7/8, 1, 1, 7/8, 1, 3/4, 5/4, 1, 1, 1] := rfl
    simp only [hw]
    norm_num
    simpa only [one_mul, sub_nonneg] using gram130 a

theorem gram_defect_bound (k : Fin 131) (a : Cell → ℝ) :
    (∑ p, (weights k p : ℝ) * monomial a p) + defect a / 4000 ≤
      (3/32 : ℝ) * (∑ j, a j ^ 2) ^ 2 := by
  have h := gram_strong k a
  linarith

theorem gram_nonneg (k : Fin 131) (a : Cell → ℝ) :
    (∑ p, (weights k p : ℝ) * monomial a p) ≤
      (3/32 : ℝ) * (∑ j, a j ^ 2) ^ 2 := by
  have h := gram_strong k a
  have hd := defect_nonneg a
  linarith

end FourRow
