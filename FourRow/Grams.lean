import FourRow.GramData
import FourRow.Grams.G000
import FourRow.Grams.G001
import FourRow.Grams.G002
import FourRow.Grams.G003
import FourRow.Grams.G004
import FourRow.Grams.G005
import FourRow.Grams.G006
import FourRow.Grams.G007
import FourRow.Grams.G008
import FourRow.Grams.G009
import FourRow.Grams.G010
import FourRow.Grams.G011
import FourRow.Grams.G012
import FourRow.Grams.G013
import FourRow.Grams.G014
import FourRow.Grams.G015
import FourRow.Grams.G016
import FourRow.Grams.G017
import FourRow.Grams.G018
import FourRow.Grams.G019
import FourRow.Grams.G020
import FourRow.Grams.G021
import FourRow.Grams.G022
import FourRow.Grams.G023
import FourRow.Grams.G024
import FourRow.Grams.G025
import FourRow.Grams.G026
import FourRow.Grams.G027
import FourRow.Grams.G028
import FourRow.Grams.G029
import FourRow.Grams.G030
import FourRow.Grams.G031
import FourRow.Grams.G032
import FourRow.Grams.G033
import FourRow.Grams.G034
import FourRow.Grams.G035
import FourRow.Grams.G036
import FourRow.Grams.G037
import FourRow.Grams.G038
import FourRow.Grams.G039
import FourRow.Grams.G040
import FourRow.Grams.G041
import FourRow.Grams.G042
import FourRow.Grams.G043
import FourRow.Grams.G044
import FourRow.Grams.G045
import FourRow.Grams.G046
import FourRow.Grams.G047
import FourRow.Grams.G048
import FourRow.Grams.G049
import FourRow.Grams.G050
import FourRow.Grams.G051
import FourRow.Grams.G052
import FourRow.Grams.G053
import FourRow.Grams.G054
import FourRow.Grams.G055
import FourRow.Grams.G056
import FourRow.Grams.G057
import FourRow.Grams.G058
import FourRow.Grams.G059
import FourRow.Grams.G060
import FourRow.Grams.G061
import FourRow.Grams.G062
import FourRow.Grams.G063
import FourRow.Grams.G064
import FourRow.Grams.G065
import FourRow.Grams.G066
import FourRow.Grams.G067
import FourRow.Grams.G068
import FourRow.Grams.G069
import FourRow.Grams.G070
import FourRow.Grams.G071
import FourRow.Grams.G072
import FourRow.Grams.G073
import FourRow.Grams.G074
import FourRow.Grams.G075
import FourRow.Grams.G076
import FourRow.Grams.G077
import FourRow.Grams.G078
import FourRow.Grams.G079
import FourRow.Grams.G080
import FourRow.Grams.G081
import FourRow.Grams.G082
import FourRow.Grams.G083
import FourRow.Grams.G084
import FourRow.Grams.G085
import FourRow.Grams.G086
import FourRow.Grams.G087
import FourRow.Grams.G088
import FourRow.Grams.G089
import FourRow.Grams.G090
import FourRow.Grams.G091
import FourRow.Grams.G092
import FourRow.Grams.G093
import FourRow.Grams.G094
import FourRow.Grams.G095
import FourRow.Grams.G096
import FourRow.Grams.G097
import FourRow.Grams.G098
import FourRow.Grams.G099
import FourRow.Grams.G100
import FourRow.Grams.G101
import FourRow.Grams.G102
import FourRow.Grams.G103
import FourRow.Grams.G104
import FourRow.Grams.G105
import FourRow.Grams.G106
import FourRow.Grams.G107
import FourRow.Grams.G108
import FourRow.Grams.G109
import FourRow.Grams.G110
import FourRow.Grams.G111
import FourRow.Grams.G112
import FourRow.Grams.G113
import FourRow.Grams.G114
import FourRow.Grams.G115
import FourRow.Grams.G116
import FourRow.Grams.G117
import FourRow.Grams.G118
import FourRow.Grams.G119
import FourRow.Grams.G120
import FourRow.Grams.G121
import FourRow.Grams.G122
import FourRow.Grams.G123
import FourRow.Grams.G124
import FourRow.Grams.G125
import FourRow.Grams.G126
import FourRow.Grams.G127
import FourRow.Grams.G128
import FourRow.Grams.G129
import FourRow.Grams.G130

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
