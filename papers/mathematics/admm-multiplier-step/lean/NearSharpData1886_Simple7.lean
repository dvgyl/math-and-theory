import NearSharpData1886Defs

namespace ADMMNearSharpCertificate.Data1886

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem Thi_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |Thi_EZ i j|) ≤ Thi_EZ i i := by decide +kernel

end ADMMNearSharpCertificate.Data1886
