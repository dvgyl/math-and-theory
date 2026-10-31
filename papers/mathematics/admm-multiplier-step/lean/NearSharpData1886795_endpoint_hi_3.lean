import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem endpoint_hi_ok_24 : ∀ i : Fin 66, 48 ≤ i.val → i.val < 50 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_25 : ∀ i : Fin 66, 50 ≤ i.val → i.val < 52 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_26 : ∀ i : Fin 66, 52 ≤ i.val → i.val < 54 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_27 : ∀ i : Fin 66, 54 ≤ i.val → i.val < 56 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_28 : ∀ i : Fin 66, 56 ≤ i.val → i.val < 58 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_29 : ∀ i : Fin 66, 58 ≤ i.val → i.val < 60 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_30 : ∀ i : Fin 66, 60 ≤ i.val → i.val < 62 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_31 : ∀ i : Fin 66, 62 ≤ i.val → i.val < 64 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
