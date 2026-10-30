import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_8 : 0 ≤ fSlope 8 ∧ 0 ≤ gSlope 8 ∧
    0 ≤ denominator * fIntercept 8 + numerator * fSlope 8 ∧
    0 ≤ denominator * gIntercept 8 + numerator * gSlope 8 := by decide

theorem row_9 : 0 ≤ fSlope 9 ∧ 0 ≤ gSlope 9 ∧
    0 ≤ denominator * fIntercept 9 + numerator * fSlope 9 ∧
    0 ≤ denominator * gIntercept 9 + numerator * gSlope 9 := by decide

theorem row_10 : 0 ≤ fSlope 10 ∧ 0 ≤ gSlope 10 ∧
    0 ≤ denominator * fIntercept 10 + numerator * fSlope 10 ∧
    0 ≤ denominator * gIntercept 10 + numerator * gSlope 10 := by decide

theorem row_11 : 0 ≤ fSlope 11 ∧ 0 ≤ gSlope 11 ∧
    0 ≤ denominator * fIntercept 11 + numerator * fSlope 11 ∧
    0 ≤ denominator * gIntercept 11 + numerator * gSlope 11 := by decide

theorem row_12 : 0 ≤ fSlope 12 ∧ 0 ≤ gSlope 12 ∧
    0 ≤ denominator * fIntercept 12 + numerator * fSlope 12 ∧
    0 ≤ denominator * gIntercept 12 + numerator * gSlope 12 := by decide

theorem row_13 : 0 ≤ fSlope 13 ∧ 0 ≤ gSlope 13 ∧
    0 ≤ denominator * fIntercept 13 + numerator * fSlope 13 ∧
    0 ≤ denominator * gIntercept 13 + numerator * gSlope 13 := by decide

theorem row_14 : 0 ≤ fSlope 14 ∧ 0 ≤ gSlope 14 ∧
    0 ≤ denominator * fIntercept 14 + numerator * fSlope 14 ∧
    0 ≤ denominator * gIntercept 14 + numerator * gSlope 14 := by decide

theorem row_15 : 0 ≤ fSlope 15 ∧ 0 ≤ gSlope 15 ∧
    0 ≤ denominator * fIntercept 15 + numerator * fSlope 15 ∧
    0 ≤ denominator * gIntercept 15 + numerator * gSlope 15 := by decide


end ADMMCycleData
