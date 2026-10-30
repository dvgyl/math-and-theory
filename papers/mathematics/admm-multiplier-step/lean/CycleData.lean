import CycleRows00
import CycleRows01
import CycleRows02
import CycleRows03
import CycleRows04
import CycleRows05
import CycleRows06
import CycleRows07
import CycleRows08
import CycleRows09
import CycleRows10
import CycleRows11
import CycleRows12
import CycleRows13
import CycleRows14
import CycleRows15

set_option autoImplicit false
set_option maxHeartbeats 0

namespace ADMMCycleData

theorem all_rows (j : I) : 0 ≤ fSlope j ∧ 0 ≤ gSlope j ∧
    0 ≤ denominator * fIntercept j + numerator * fSlope j ∧
    0 ≤ denominator * gIntercept j + numerator * gSlope j := by
  fin_cases j
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
  · exact row_64
  · exact row_65
  · exact row_66
  · exact row_67
  · exact row_68
  · exact row_69
  · exact row_70
  · exact row_71
  · exact row_72
  · exact row_73
  · exact row_74
  · exact row_75
  · exact row_76
  · exact row_77
  · exact row_78
  · exact row_79
  · exact row_80
  · exact row_81
  · exact row_82
  · exact row_83
  · exact row_84
  · exact row_85
  · exact row_86
  · exact row_87
  · exact row_88
  · exact row_89
  · exact row_90
  · exact row_91
  · exact row_92
  · exact row_93
  · exact row_94
  · exact row_95
  · exact row_96
  · exact row_97
  · exact row_98
  · exact row_99
  · exact row_100
  · exact row_101
  · exact row_102
  · exact row_103
  · exact row_104
  · exact row_105
  · exact row_106
  · exact row_107
  · exact row_108
  · exact row_109
  · exact row_110
  · exact row_111
  · exact row_112
  · exact row_113
  · exact row_114
  · exact row_115
  · exact row_116
  · exact row_117
  · exact row_118
  · exact row_119
  · exact row_120
  · exact row_121
  · exact row_122
  · exact row_123
  · exact row_124
  · exact row_125
  · exact row_126
  · exact row_127

end ADMMCycleData

#print axioms ADMMCycleData.all_rows
