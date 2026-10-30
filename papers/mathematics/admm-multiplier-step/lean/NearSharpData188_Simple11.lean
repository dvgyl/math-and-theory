import NearSharpData188Defs

namespace ADMMNearSharpCertificate.Data188

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem lambdaGZ_flow : ∀ i : Fin 13, (∑ j, lambdaGZ i j) = ∑ j, lambdaGZ j i := by decide +kernel

end ADMMNearSharpCertificate.Data188
