import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_16 : 0 ≤ fSlope 16 ∧ 0 ≤ gSlope 16 ∧
    0 ≤ denominator * fIntercept 16 + numerator * fSlope 16 ∧
    0 ≤ denominator * gIntercept 16 + numerator * gSlope 16 := by decide

theorem row_17 : 0 ≤ fSlope 17 ∧ 0 ≤ gSlope 17 ∧
    0 ≤ denominator * fIntercept 17 + numerator * fSlope 17 ∧
    0 ≤ denominator * gIntercept 17 + numerator * gSlope 17 := by decide

theorem row_18 : 0 ≤ fSlope 18 ∧ 0 ≤ gSlope 18 ∧
    0 ≤ denominator * fIntercept 18 + numerator * fSlope 18 ∧
    0 ≤ denominator * gIntercept 18 + numerator * gSlope 18 := by decide

theorem row_19 : 0 ≤ fSlope 19 ∧ 0 ≤ gSlope 19 ∧
    0 ≤ denominator * fIntercept 19 + numerator * fSlope 19 ∧
    0 ≤ denominator * gIntercept 19 + numerator * gSlope 19 := by decide

theorem row_20 : 0 ≤ fSlope 20 ∧ 0 ≤ gSlope 20 ∧
    0 ≤ denominator * fIntercept 20 + numerator * fSlope 20 ∧
    0 ≤ denominator * gIntercept 20 + numerator * gSlope 20 := by decide

theorem row_21 : 0 ≤ fSlope 21 ∧ 0 ≤ gSlope 21 ∧
    0 ≤ denominator * fIntercept 21 + numerator * fSlope 21 ∧
    0 ≤ denominator * gIntercept 21 + numerator * gSlope 21 := by decide

theorem row_22 : 0 ≤ fSlope 22 ∧ 0 ≤ gSlope 22 ∧
    0 ≤ denominator * fIntercept 22 + numerator * fSlope 22 ∧
    0 ≤ denominator * gIntercept 22 + numerator * gSlope 22 := by decide

theorem row_23 : 0 ≤ fSlope 23 ∧ 0 ≤ gSlope 23 ∧
    0 ≤ denominator * fIntercept 23 + numerator * fSlope 23 ∧
    0 ≤ denominator * gIntercept 23 + numerator * gSlope 23 := by decide


end ADMMCycleData
