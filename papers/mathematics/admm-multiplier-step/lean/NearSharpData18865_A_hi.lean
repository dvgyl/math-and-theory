import NearSharpData18865Defs

namespace ADMMNearSharpCertificate.Data18865

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem A_hi_ok_0 : ∀ k : Fin 42, 0 ≤ k.val → k.val < 42 → 
    A_hiL.getD k.val [] = lin3N tauDen_hi (-tauNum_hi) (-tauDen_hi) 21 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) := by
  decide +kernel

end ADMMNearSharpCertificate.Data18865
