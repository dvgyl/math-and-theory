import NearSharpData188632Defs

namespace ADMMNearSharpCertificate.Data188632

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem weightedFZ_ok_0 : ∀ i : Fin 21, 0 ≤ i.val → i.val < 8 → ∀ k : Fin 42,
    dotN 21 (lambdaFL.getD i.val []) (xRowsL.getD k.val []) - (xRowsL.getD k.val []).getD i.val 0 * sumN 21 (lambdaFL.getD i.val []) = weightedFZ i k := by
  decide +kernel

theorem weightedFZ_ok_1 : ∀ i : Fin 21, 8 ≤ i.val → i.val < 16 → ∀ k : Fin 42,
    dotN 21 (lambdaFL.getD i.val []) (xRowsL.getD k.val []) - (xRowsL.getD k.val []).getD i.val 0 * sumN 21 (lambdaFL.getD i.val []) = weightedFZ i k := by
  decide +kernel

theorem weightedFZ_ok_2 : ∀ i : Fin 21, 16 ≤ i.val → i.val < 21 → ∀ k : Fin 42,
    dotN 21 (lambdaFL.getD i.val []) (xRowsL.getD k.val []) - (xRowsL.getD k.val []).getD i.val 0 * sumN 21 (lambdaFL.getD i.val []) = weightedFZ i k := by
  decide +kernel

end ADMMNearSharpCertificate.Data188632
