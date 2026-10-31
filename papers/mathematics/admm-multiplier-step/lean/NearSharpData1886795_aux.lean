import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem lower_lo_dd_ok : ∀ i : Fin 64, absSumN 64 (lower_lo_EL.getD i.val []) ≤ lower_lo_EZ i i + |lower_lo_EZ i i| := by
  decide +kernel

theorem Tlo_dd_ok : ∀ i : Fin 64, absSumN 64 (Tlo_EL.getD i.val []) ≤ Tlo_EZ i i + |Tlo_EZ i i| := by
  decide +kernel

theorem lower_hi_dd_ok : ∀ i : Fin 64, absSumN 64 (lower_hi_EL.getD i.val []) ≤ lower_hi_EZ i i + |lower_hi_EZ i i| := by
  decide +kernel

theorem Thi_dd_ok : ∀ i : Fin 64, absSumN 64 (Thi_EL.getD i.val []) ≤ Thi_EZ i i + |Thi_EZ i i| := by
  decide +kernel

theorem lambdaFZ_nonneg : ∀ i j : Fin 33, 0 ≤ lambdaFZ i j := by decide +kernel

theorem lambdaFZ_flow : ∀ i : Fin 33, (∑ j, lambdaFZ i j) = ∑ j, lambdaFZ j i := by decide +kernel

theorem lambdaGZ_nonneg : ∀ i j : Fin 33, 0 ≤ lambdaGZ i j := by decide +kernel

theorem lambdaGZ_flow : ∀ i : Fin 33, (∑ j, lambdaGZ i j) = ∑ j, lambdaGZ j i := by decide +kernel

end ADMMNearSharpCertificate.Data1886795
