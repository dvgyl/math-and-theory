import NearSharpData188628Defs

namespace ADMMNearSharpCertificate.Data188628

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem lower_hi_residual_upper_symmetric_0 : ∀ i : Fin 40, 0 ≤ i.val → i.val < 16 → ∀ j : Fin 40, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_1 : ∀ i : Fin 40, 16 ≤ i.val → i.val < 32 → ∀ j : Fin 40, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

theorem lower_hi_residual_upper_symmetric_2 : ∀ i : Fin 40, 32 ≤ i.val → i.val < 40 → ∀ j : Fin 40, i.val < j.val →
    lower_hi_EZ i j = lower_hi_EZ j i := by
  decide +kernel

end ADMMNearSharpCertificate.Data188628
