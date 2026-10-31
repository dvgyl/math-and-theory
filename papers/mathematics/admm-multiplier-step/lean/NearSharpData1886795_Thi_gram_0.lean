import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem Thi_gram_ok_0 : ∀ i : Fin 64, 0 ≤ i.val → i.val < 2 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_1 : ∀ i : Fin 64, 2 ≤ i.val → i.val < 4 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_2 : ∀ i : Fin 64, 4 ≤ i.val → i.val < 6 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_3 : ∀ i : Fin 64, 6 ≤ i.val → i.val < 8 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_4 : ∀ i : Fin 64, 8 ≤ i.val → i.val < 10 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_5 : ∀ i : Fin 64, 10 ≤ i.val → i.val < 12 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_6 : ∀ i : Fin 64, 12 ≤ i.val → i.val < 14 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

theorem Thi_gram_ok_7 : ∀ i : Fin 64, 14 ≤ i.val → i.val < 16 → ∀ j : Fin 64,
    Thi_Rden ^ 2 * ThiZ i j = den_hi * dotN 64 (Thi_RL.getD i.val []) (Thi_RL.getD j.val []) + Thi_EZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
