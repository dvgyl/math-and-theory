import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_0 : 0 ≤ fSlope 0 ∧ 0 ≤ gSlope 0 ∧
    0 ≤ denominator * fIntercept 0 + numerator * fSlope 0 ∧
    0 ≤ denominator * gIntercept 0 + numerator * gSlope 0 := by decide

theorem row_1 : 0 ≤ fSlope 1 ∧ 0 ≤ gSlope 1 ∧
    0 ≤ denominator * fIntercept 1 + numerator * fSlope 1 ∧
    0 ≤ denominator * gIntercept 1 + numerator * gSlope 1 := by decide

theorem row_2 : 0 ≤ fSlope 2 ∧ 0 ≤ gSlope 2 ∧
    0 ≤ denominator * fIntercept 2 + numerator * fSlope 2 ∧
    0 ≤ denominator * gIntercept 2 + numerator * gSlope 2 := by decide

theorem row_3 : 0 ≤ fSlope 3 ∧ 0 ≤ gSlope 3 ∧
    0 ≤ denominator * fIntercept 3 + numerator * fSlope 3 ∧
    0 ≤ denominator * gIntercept 3 + numerator * gSlope 3 := by decide

theorem row_4 : 0 ≤ fSlope 4 ∧ 0 ≤ gSlope 4 ∧
    0 ≤ denominator * fIntercept 4 + numerator * fSlope 4 ∧
    0 ≤ denominator * gIntercept 4 + numerator * gSlope 4 := by decide

theorem row_5 : 0 ≤ fSlope 5 ∧ 0 ≤ gSlope 5 ∧
    0 ≤ denominator * fIntercept 5 + numerator * fSlope 5 ∧
    0 ≤ denominator * gIntercept 5 + numerator * gSlope 5 := by decide

theorem row_6 : 0 ≤ fSlope 6 ∧ 0 ≤ gSlope 6 ∧
    0 ≤ denominator * fIntercept 6 + numerator * fSlope 6 ∧
    0 ≤ denominator * gIntercept 6 + numerator * gSlope 6 := by decide

theorem row_7 : 0 ≤ fSlope 7 ∧ 0 ≤ gSlope 7 ∧
    0 ≤ denominator * fIntercept 7 + numerator * fSlope 7 ∧
    0 ≤ denominator * gIntercept 7 + numerator * gSlope 7 := by decide


end ADMMCycleData
