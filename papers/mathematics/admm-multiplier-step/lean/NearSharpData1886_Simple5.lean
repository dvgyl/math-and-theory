import NearSharpData1886Defs

namespace ADMMNearSharpCertificate.Data1886

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem lower_hi_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |lower_hi_EZ i j|) ≤ lower_hi_EZ i i := by decide +kernel

end ADMMNearSharpCertificate.Data1886
