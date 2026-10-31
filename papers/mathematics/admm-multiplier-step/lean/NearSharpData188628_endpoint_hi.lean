import NearSharpData188628Defs

namespace ADMMNearSharpCertificate.Data188628

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem endpoint_hi_ok_0 : ∀ i : Fin 42, 0 ≤ i.val → i.val < 4 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_1 : ∀ i : Fin 42, 4 ≤ i.val → i.val < 8 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_2 : ∀ i : Fin 42, 8 ≤ i.val → i.val < 12 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_3 : ∀ i : Fin 42, 12 ≤ i.val → i.val < 16 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_4 : ∀ i : Fin 42, 16 ≤ i.val → i.val < 20 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_5 : ∀ i : Fin 42, 20 ≤ i.val → i.val < 24 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_6 : ∀ i : Fin 42, 24 ≤ i.val → i.val < 28 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_7 : ∀ i : Fin 42, 28 ≤ i.val → i.val < 32 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_8 : ∀ i : Fin 42, 32 ≤ i.val → i.val < 36 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_9 : ∀ i : Fin 42, 36 ≤ i.val → i.val < 40 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

theorem endpoint_hi_ok_10 : ∀ i : Fin 42, 40 ≤ i.val → i.val < 42 → ∀ j : Fin 42,
    embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j +
      qFactor_hi * ((dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
        (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val []))) =
      embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data188628
