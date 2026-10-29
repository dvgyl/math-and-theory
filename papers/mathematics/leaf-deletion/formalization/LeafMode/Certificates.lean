import LeafMode.AlgebraCertificate
import LeafMode.ShapeCertificate

namespace LeafMode.Cert
open Polynomial

theorem pData_formula : ofList pData = P := by
  simp only [pData, ofList_add, ofList_cons, ofList_scale, C_0, zero_add]
  rw [f_power, g_power, h_power, sList_formula, tList_formula, bList_formula]
  unfold P
  simp [sub_eq_add_neg, add_assoc]

theorem qData_formula : ofList qData = Q := by
  simp only [qData, ofList_add, ofList_cons, C_0, zero_add]
  rw [f_power, g_power, sList_formula, tList_formula]
  unfold Q
  ring

theorem p_up (i : ℕ) (hi : i < 3314) : P.coeff i ≤ P.coeff (i+1) := by
  rw [← pData_formula]
  exact p_data_up i hi

theorem p_down (i : ℕ) (hi : 3314 ≤ i) : P.coeff (i+1) ≤ P.coeff i := by
  rw [← pData_formula]
  exact p_data_down i hi

theorem q_up (i : ℕ) (hi : i < 3315) : Q.coeff i ≤ Q.coeff (i+1) := by
  rw [← qData_formula]
  exact q_data_up i hi

theorem q_down (i : ℕ) (hi : 3315 ≤ i) : Q.coeff (i+1) ≤ Q.coeff i := by
  rw [← qData_formula]
  exact q_data_down i hi

theorem p_nonneg (i : ℕ) : 0 ≤ P.coeff i := by
  rw [← pData_formula]
  exact nonneg_of_all pData p_nonneg_checked i

theorem q_nonneg (i : ℕ) : 0 ≤ Q.coeff i := by
  rw [← qData_formula]
  exact nonneg_of_all qData q_nonneg_checked i

theorem p_positive : 0 < P.coeff 3314 := by
  rw [← pData_formula, coeff_ofList]
  exact p_positive_checked

theorem q_positive : 0 < Q.coeff 3315 := by
  rw [← qData_formula, coeff_ofList]
  exact q_positive_checked

theorem p_unique (k : ℕ) (hk : k ≠ 3314) : P.coeff k < P.coeff 3314 := by
  apply peak_unique P.coeff 3314 (by decide) p_up p_down _ _ k hk
  · rw [← pData_formula, coeff_ofList, coeff_ofList]
    exact p_left_checked
  · rw [← pData_formula, coeff_ofList, coeff_ofList]
    exact p_right_checked

theorem q_unique (k : ℕ) (hk : k ≠ 3315) : Q.coeff k < Q.coeff 3315 := by
  apply peak_unique Q.coeff 3315 (by decide) q_up q_down _ _ k hk
  · rw [← qData_formula, coeff_ofList, coeff_ofList]
    exact q_left_checked
  · rw [← qData_formula, coeff_ofList, coeff_ofList]
    exact q_right_checked

#print axioms p_unique
#print axioms q_unique
end LeafMode.Cert
