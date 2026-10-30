import NearSharpData1886Defs

namespace ADMMNearSharpCertificate.Data1886

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem lambdaFZ_nonneg : ∀ i j : Fin 21, 0 ≤ lambdaFZ i j := by decide +kernel

end ADMMNearSharpCertificate.Data1886
