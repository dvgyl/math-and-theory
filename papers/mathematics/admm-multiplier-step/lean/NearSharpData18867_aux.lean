import NearSharpData18867Defs

namespace ADMMNearSharpCertificate.Data18867

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem lower_lo_dd_ok : ∀ i : Fin 40, absSumN 40 (lower_lo_EL.getD i.val []) ≤ lower_lo_EZ i i + |lower_lo_EZ i i| := by
  decide +kernel

theorem Tlo_dd_ok : ∀ i : Fin 40, absSumN 40 (Tlo_EL.getD i.val []) ≤ Tlo_EZ i i + |Tlo_EZ i i| := by
  decide +kernel

theorem lower_hi_dd_ok : ∀ i : Fin 40, absSumN 40 (lower_hi_EL.getD i.val []) ≤ lower_hi_EZ i i + |lower_hi_EZ i i| := by
  decide +kernel

theorem Thi_dd_ok : ∀ i : Fin 40, absSumN 40 (Thi_EL.getD i.val []) ≤ Thi_EZ i i + |Thi_EZ i i| := by
  decide +kernel

theorem lambdaFZ_nonneg : ∀ i j : Fin 21, 0 ≤ lambdaFZ i j := by decide +kernel

theorem lambdaFZ_flow : ∀ i : Fin 21, (∑ j, lambdaFZ i j) = ∑ j, lambdaFZ j i := by decide +kernel

theorem lambdaGZ_nonneg : ∀ i j : Fin 21, 0 ≤ lambdaGZ i j := by decide +kernel

theorem lambdaGZ_flow : ∀ i : Fin 21, (∑ j, lambdaGZ i j) = ∑ j, lambdaGZ j i := by decide +kernel

end ADMMNearSharpCertificate.Data18867
