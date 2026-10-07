module

public import FourRow.GramData
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
  fin_cases k
  · convert (gram000 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram001 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram002 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram003 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram004 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram005 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram006 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram007 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram008 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram009 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram010 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram011 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram012 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram013 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram014 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram015 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram016 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram017 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram018 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram019 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram020 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram021 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram022 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram023 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram024 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram025 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram026 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram027 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram028 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram029 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram030 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram031 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram032 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram033 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram034 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram035 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram036 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram037 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram038 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram039 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram040 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram041 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram042 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram043 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram044 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram045 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram046 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram047 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram048 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram049 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram050 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram051 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram052 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram053 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram054 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram055 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram056 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram057 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram058 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram059 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram060 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram061 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram062 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram063 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram064 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram065 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram066 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram067 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram068 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram069 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram070 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram071 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram072 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram073 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram074 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram075 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram076 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram077 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram078 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram079 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram080 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram081 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram082 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram083 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram084 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram085 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram086 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram087 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram088 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram089 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram090 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram091 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram092 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram093 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram094 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram095 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram096 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram097 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram098 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram099 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram100 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram101 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram102 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram103 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram104 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram105 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram106 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram107 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram108 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram109 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram110 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram111 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram112 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram113 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram114 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram115 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram116 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram117 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram118 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram119 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram120 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram121 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram122 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram123 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram124 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram125 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram126 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram127 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram128 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram129 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring
  · convert (gram130 a) using 1 <;>
      norm_num [weights, defect, monomial, cell, permutation, Fin.sum_univ_succ, Fin.prod_univ_succ] <;>
      ring

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
