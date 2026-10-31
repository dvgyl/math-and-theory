import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem weightedGZ_ok_0 : ∀ i : Fin 33, 0 ≤ i.val → i.val < 4 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_1 : ∀ i : Fin 33, 4 ≤ i.val → i.val < 8 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_2 : ∀ i : Fin 33, 8 ≤ i.val → i.val < 12 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_3 : ∀ i : Fin 33, 12 ≤ i.val → i.val < 16 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_4 : ∀ i : Fin 33, 16 ≤ i.val → i.val < 20 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_5 : ∀ i : Fin 33, 20 ≤ i.val → i.val < 24 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_6 : ∀ i : Fin 33, 24 ≤ i.val → i.val < 28 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

theorem weightedGZ_ok_7 : ∀ i : Fin 33, 28 ≤ i.val → i.val < 32 → ∀ k : Fin 66,
    dotN 33 (lambdaGL.getD i.val []) (zRowsL.getD k.val []) - (zRowsL.getD k.val []).getD i.val 0 * sumN 33 (lambdaGL.getD i.val []) = weightedGZ i k := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
