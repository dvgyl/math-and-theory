import CycleDataCore

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace ADMMCycleData

theorem row_64 : 0 ≤ fSlope 64 ∧ 0 ≤ gSlope 64 ∧
    0 ≤ denominator * fIntercept 64 + numerator * fSlope 64 ∧
    0 ≤ denominator * gIntercept 64 + numerator * gSlope 64 := by decide

theorem row_65 : 0 ≤ fSlope 65 ∧ 0 ≤ gSlope 65 ∧
    0 ≤ denominator * fIntercept 65 + numerator * fSlope 65 ∧
    0 ≤ denominator * gIntercept 65 + numerator * gSlope 65 := by decide

theorem row_66 : 0 ≤ fSlope 66 ∧ 0 ≤ gSlope 66 ∧
    0 ≤ denominator * fIntercept 66 + numerator * fSlope 66 ∧
    0 ≤ denominator * gIntercept 66 + numerator * gSlope 66 := by decide

theorem row_67 : 0 ≤ fSlope 67 ∧ 0 ≤ gSlope 67 ∧
    0 ≤ denominator * fIntercept 67 + numerator * fSlope 67 ∧
    0 ≤ denominator * gIntercept 67 + numerator * gSlope 67 := by decide

theorem row_68 : 0 ≤ fSlope 68 ∧ 0 ≤ gSlope 68 ∧
    0 ≤ denominator * fIntercept 68 + numerator * fSlope 68 ∧
    0 ≤ denominator * gIntercept 68 + numerator * gSlope 68 := by decide

theorem row_69 : 0 ≤ fSlope 69 ∧ 0 ≤ gSlope 69 ∧
    0 ≤ denominator * fIntercept 69 + numerator * fSlope 69 ∧
    0 ≤ denominator * gIntercept 69 + numerator * gSlope 69 := by decide

theorem row_70 : 0 ≤ fSlope 70 ∧ 0 ≤ gSlope 70 ∧
    0 ≤ denominator * fIntercept 70 + numerator * fSlope 70 ∧
    0 ≤ denominator * gIntercept 70 + numerator * gSlope 70 := by decide

theorem row_71 : 0 ≤ fSlope 71 ∧ 0 ≤ gSlope 71 ∧
    0 ≤ denominator * fIntercept 71 + numerator * fSlope 71 ∧
    0 ≤ denominator * gIntercept 71 + numerator * gSlope 71 := by decide


end ADMMCycleData
