import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem endpoint_lo_ok_32 : ∀ i : Fin 66, 64 ≤ i.val → i.val < 66 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
