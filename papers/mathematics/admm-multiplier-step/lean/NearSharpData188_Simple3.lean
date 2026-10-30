import NearSharpData188Defs

namespace ADMMNearSharpCertificate.Data188

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic

theorem Tlo_residual_dd : ∀ i : Fin 24, (∑ j ∈ Finset.univ.erase i, |Tlo_EZ i j|) ≤ Tlo_EZ i i := by decide +kernel

end ADMMNearSharpCertificate.Data188
