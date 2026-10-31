import NearSharpData1886795Defs

namespace ADMMNearSharpCertificate.Data1886795

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open ADMMNearSharpCertificate.IntArithmetic ADMMNearSharpCertificate.IntLists

theorem lower_lo_gram_ok_16 : ∀ i : Fin 64, 32 ≤ i.val → i.val < 34 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_17 : ∀ i : Fin 64, 34 ≤ i.val → i.val < 36 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_18 : ∀ i : Fin 64, 36 ≤ i.val → i.val < 38 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_19 : ∀ i : Fin 64, 38 ≤ i.val → i.val < 40 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_20 : ∀ i : Fin 64, 40 ≤ i.val → i.val < 42 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_21 : ∀ i : Fin 64, 42 ≤ i.val → i.val < 44 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_22 : ∀ i : Fin 64, 44 ≤ i.val → i.val < 46 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

theorem lower_lo_gram_ok_23 : ∀ i : Fin 64, 46 ≤ i.val → i.val < 48 → ∀ j : Fin 64,
    lower_lo_Rden ^ 2 * lower_loZ i j = den_lo * dotN 64 (lower_lo_RL.getD i.val []) (lower_lo_RL.getD j.val []) + lower_lo_EZ i j := by
  decide +kernel

end ADMMNearSharpCertificate.Data1886795
