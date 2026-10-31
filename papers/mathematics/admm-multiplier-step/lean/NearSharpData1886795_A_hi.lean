import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem A_hi_ok_0 : ∀ k : Fin 66, 0 ≤ k.val → k.val < 66 → 
    A_hiL.getD k.val [] = lin3N tauDen_hi (-tauNum_hi) (-tauDen_hi) 33 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
