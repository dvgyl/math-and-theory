import NearSharpData18865Defs

namespace ADMMNearSharpCertificate.Data18865

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem Tlo_gram_ok_0 : ∀ i : Fin 40, 0 ≤ i.val → i.val < 4 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_1 : ∀ i : Fin 40, 4 ≤ i.val → i.val < 8 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_2 : ∀ i : Fin 40, 8 ≤ i.val → i.val < 12 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_3 : ∀ i : Fin 40, 12 ≤ i.val → i.val < 16 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_4 : ∀ i : Fin 40, 16 ≤ i.val → i.val < 20 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_5 : ∀ i : Fin 40, 20 ≤ i.val → i.val < 24 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_6 : ∀ i : Fin 40, 24 ≤ i.val → i.val < 28 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_7 : ∀ i : Fin 40, 28 ≤ i.val → i.val < 32 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_8 : ∀ i : Fin 40, 32 ≤ i.val → i.val < 36 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

theorem Tlo_gram_ok_9 : ∀ i : Fin 40, 36 ≤ i.val → i.val < 40 → ∀ j : Fin 40,
    Tlo_Rden ^ 2 * TloZ i j = den_lo * dotN 40 (Tlo_RL.getD i.val []) (Tlo_RL.getD j.val []) + Tlo_EZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data18865
