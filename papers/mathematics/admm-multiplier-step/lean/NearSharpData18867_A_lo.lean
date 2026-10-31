import NearSharpData18867Defs

namespace ADMMNearSharpCertificate.Data18867

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem A_lo_ok_0 : ∀ k : Fin 42, 0 ≤ k.val → k.val < 42 → 
    A_loL.getD k.val [] = lin3N tauDen_lo (-tauNum_lo) (-tauDen_lo) 21 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) := by
  decide +kernel

end ADMMNearSharpCertificate.Data18867
