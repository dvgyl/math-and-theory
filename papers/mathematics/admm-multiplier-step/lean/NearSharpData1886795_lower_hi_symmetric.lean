import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem lower_hi_residual_upper_symmetric_0 : ∀ i : Fin 64, 0 ≤ i.val → i.val < 8 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_1 : ∀ i : Fin 64, 8 ≤ i.val → i.val < 16 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_2 : ∀ i : Fin 64, 16 ≤ i.val → i.val < 24 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_3 : ∀ i : Fin 64, 24 ≤ i.val → i.val < 32 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_4 : ∀ i : Fin 64, 32 ≤ i.val → i.val < 40 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_5 : ∀ i : Fin 64, 40 ≤ i.val → i.val < 48 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_6 : ∀ i : Fin 64, 48 ≤ i.val → i.val < 56 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_7 : ∀ i : Fin 64, 56 ≤ i.val → i.val < 64 → ∀ j : Fin 64, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
