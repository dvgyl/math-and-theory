import NearSharpData188Defs

namespace ADMMNearSharpCertificate.Data188

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem Tlo_residual_symmetric : ∀ i j : Fin 24, Tlo_EZ i j = Tlo_EZ j i := by decide +kernel

end ADMMNearSharpCertificate.Data188
