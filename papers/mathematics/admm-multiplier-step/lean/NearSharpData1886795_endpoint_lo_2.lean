import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem endpoint_lo_ok_16 : ∀ i : Fin 66, 32 ≤ i.val → i.val < 34 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_17 : ∀ i : Fin 66, 34 ≤ i.val → i.val < 36 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_18 : ∀ i : Fin 66, 36 ≤ i.val → i.val < 38 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_19 : ∀ i : Fin 66, 38 ≤ i.val → i.val < 40 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_20 : ∀ i : Fin 66, 40 ≤ i.val → i.val < 42 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_21 : ∀ i : Fin 66, 42 ≤ i.val → i.val < 44 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_22 : ∀ i : Fin 66, 44 ≤ i.val → i.val < 46 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

theorem endpoint_lo_ok_23 : ∀ i : Fin 66, 46 ≤ i.val → i.val < 48 → ∀ j : Fin 66,
    embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j +
      qFactor_lo * ((dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
        (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val []))) =
      embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
