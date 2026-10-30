import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_120 : 0 ≤ fSlope 120 ∧ 0 ≤ gSlope 120 ∧
    0 ≤ denominator * fIntercept 120 + numerator * fSlope 120 ∧
    0 ≤ denominator * gIntercept 120 + numerator * gSlope 120 := by decide +kernel

theorem row_121 : 0 ≤ fSlope 121 ∧ 0 ≤ gSlope 121 ∧
    0 ≤ denominator * fIntercept 121 + numerator * fSlope 121 ∧
    0 ≤ denominator * gIntercept 121 + numerator * gSlope 121 := by decide +kernel

theorem row_122 : 0 ≤ fSlope 122 ∧ 0 ≤ gSlope 122 ∧
    0 ≤ denominator * fIntercept 122 + numerator * fSlope 122 ∧
    0 ≤ denominator * gIntercept 122 + numerator * gSlope 122 := by decide +kernel

theorem row_123 : 0 ≤ fSlope 123 ∧ 0 ≤ gSlope 123 ∧
    0 ≤ denominator * fIntercept 123 + numerator * fSlope 123 ∧
    0 ≤ denominator * gIntercept 123 + numerator * gSlope 123 := by decide +kernel

theorem row_124 : 0 ≤ fSlope 124 ∧ 0 ≤ gSlope 124 ∧
    0 ≤ denominator * fIntercept 124 + numerator * fSlope 124 ∧
    0 ≤ denominator * gIntercept 124 + numerator * gSlope 124 := by decide +kernel

theorem row_125 : 0 ≤ fSlope 125 ∧ 0 ≤ gSlope 125 ∧
    0 ≤ denominator * fIntercept 125 + numerator * fSlope 125 ∧
    0 ≤ denominator * gIntercept 125 + numerator * gSlope 125 := by decide +kernel

theorem row_126 : 0 ≤ fSlope 126 ∧ 0 ≤ gSlope 126 ∧
    0 ≤ denominator * fIntercept 126 + numerator * fSlope 126 ∧
    0 ≤ denominator * gIntercept 126 + numerator * gSlope 126 := by decide +kernel

theorem row_127 : 0 ≤ fSlope 127 ∧ 0 ≤ gSlope 127 ∧
    0 ≤ denominator * fIntercept 127 + numerator * fSlope 127 ∧
    0 ≤ denominator * gIntercept 127 + numerator * gSlope 127 := by decide +kernel


end ADMMCycleData
