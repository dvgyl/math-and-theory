import NearSharpData188632Defs

namespace ADMMNearSharpCertificate.Data188632

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem Tlo_residual_upper_symmetric_0 : ∀ i : Fin 40, 0 ≤ i.val → i.val < 16 → ∀ j : Fin 40, i.val < j.val →
    Tlo_EZ i j = Tlo_EZ j i := by
  decide +kernel

theorem Tlo_residual_upper_symmetric_1 : ∀ i : Fin 40, 16 ≤ i.val → i.val < 32 → ∀ j : Fin 40, i.val < j.val →
    Tlo_EZ i j = Tlo_EZ j i := by
  decide +kernel

theorem Tlo_residual_upper_symmetric_2 : ∀ i : Fin 40, 32 ≤ i.val → i.val < 40 → ∀ j : Fin 40, i.val < j.val →
    Tlo_EZ i j = Tlo_EZ j i := by
  decide +kernel

end ADMMNearSharpCertificate.Data188632
