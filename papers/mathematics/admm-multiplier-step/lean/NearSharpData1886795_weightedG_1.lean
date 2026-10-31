import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem weightedGZ_ok_8 : ∀ i : Fin 33, 32 ≤ i.val → i.val < 33 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
