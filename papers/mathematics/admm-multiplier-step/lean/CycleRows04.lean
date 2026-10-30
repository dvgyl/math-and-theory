import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_32 : 0 ≤ fSlope 32 ∧ 0 ≤ gSlope 32 ∧
    0 ≤ denominator * fIntercept 32 + numerator * fSlope 32 ∧
    0 ≤ denominator * gIntercept 32 + numerator * gSlope 32 := by decide

theorem row_33 : 0 ≤ fSlope 33 ∧ 0 ≤ gSlope 33 ∧
    0 ≤ denominator * fIntercept 33 + numerator * fSlope 33 ∧
    0 ≤ denominator * gIntercept 33 + numerator * gSlope 33 := by decide

theorem row_34 : 0 ≤ fSlope 34 ∧ 0 ≤ gSlope 34 ∧
    0 ≤ denominator * fIntercept 34 + numerator * fSlope 34 ∧
    0 ≤ denominator * gIntercept 34 + numerator * gSlope 34 := by decide

theorem row_35 : 0 ≤ fSlope 35 ∧ 0 ≤ gSlope 35 ∧
    0 ≤ denominator * fIntercept 35 + numerator * fSlope 35 ∧
    0 ≤ denominator * gIntercept 35 + numerator * gSlope 35 := by decide

theorem row_36 : 0 ≤ fSlope 36 ∧ 0 ≤ gSlope 36 ∧
    0 ≤ denominator * fIntercept 36 + numerator * fSlope 36 ∧
    0 ≤ denominator * gIntercept 36 + numerator * gSlope 36 := by decide

theorem row_37 : 0 ≤ fSlope 37 ∧ 0 ≤ gSlope 37 ∧
    0 ≤ denominator * fIntercept 37 + numerator * fSlope 37 ∧
    0 ≤ denominator * gIntercept 37 + numerator * gSlope 37 := by decide

theorem row_38 : 0 ≤ fSlope 38 ∧ 0 ≤ gSlope 38 ∧
    0 ≤ denominator * fIntercept 38 + numerator * fSlope 38 ∧
    0 ≤ denominator * gIntercept 38 + numerator * gSlope 38 := by decide

theorem row_39 : 0 ≤ fSlope 39 ∧ 0 ≤ gSlope 39 ∧
    0 ≤ denominator * fIntercept 39 + numerator * fSlope 39 ∧
    0 ≤ denominator * gIntercept 39 + numerator * gSlope 39 := by decide


end ADMMCycleData
