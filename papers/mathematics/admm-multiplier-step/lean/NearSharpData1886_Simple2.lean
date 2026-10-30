import NearSharpData1886Defs

namespace ADMMNearSharpCertificate.Data1886

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem Tlo_residual_symmetric : ∀ i j : Fin 40, Tlo_EZ i j = Tlo_EZ j i := by decide +kernel

end ADMMNearSharpCertificate.Data1886
