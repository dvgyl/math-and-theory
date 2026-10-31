import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem endpoint_hi_ok_0 : ∀ i : Fin 66, 0 ≤ i.val → i.val < 2 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_1 : ∀ i : Fin 66, 2 ≤ i.val → i.val < 4 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_2 : ∀ i : Fin 66, 4 ≤ i.val → i.val < 6 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_3 : ∀ i : Fin 66, 6 ≤ i.val → i.val < 8 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_4 : ∀ i : Fin 66, 8 ≤ i.val → i.val < 10 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_5 : ∀ i : Fin 66, 10 ≤ i.val → i.val < 12 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_6 : ∀ i : Fin 66, 12 ≤ i.val → i.val < 14 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_7 : ∀ i : Fin 66, 14 ≤ i.val → i.val < 16 → ∀ j : Fin 66,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
