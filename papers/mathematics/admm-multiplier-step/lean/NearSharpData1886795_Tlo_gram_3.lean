import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem Tlo_gram_ok_24 : ∀ i : Fin 64, 48 ≤ i.val → i.val < 50 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_25 : ∀ i : Fin 64, 50 ≤ i.val → i.val < 52 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_26 : ∀ i : Fin 64, 52 ≤ i.val → i.val < 54 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_27 : ∀ i : Fin 64, 54 ≤ i.val → i.val < 56 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_28 : ∀ i : Fin 64, 56 ≤ i.val → i.val < 58 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_29 : ∀ i : Fin 64, 58 ≤ i.val → i.val < 60 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_30 : ∀ i : Fin 64, 60 ≤ i.val → i.val < 62 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_31 : ∀ i : Fin 64, 62 ≤ i.val → i.val < 64 → ∀ j : Fin 64,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 64 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
