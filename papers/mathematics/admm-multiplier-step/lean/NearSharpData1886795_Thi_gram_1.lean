import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem Thi_gram_ok_8 : ∀ i : Fin 64, 16 ≤ i.val → i.val < 18 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_9 : ∀ i : Fin 64, 18 ≤ i.val → i.val < 20 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_10 : ∀ i : Fin 64, 20 ≤ i.val → i.val < 22 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_11 : ∀ i : Fin 64, 22 ≤ i.val → i.val < 24 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_12 : ∀ i : Fin 64, 24 ≤ i.val → i.val < 26 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_13 : ∀ i : Fin 64, 26 ≤ i.val → i.val < 28 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_14 : ∀ i : Fin 64, 28 ≤ i.val → i.val < 30 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_15 : ∀ i : Fin 64, 30 ≤ i.val → i.val < 32 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
