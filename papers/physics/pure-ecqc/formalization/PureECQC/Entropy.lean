import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact Shannon mutual informations for the pure five-dimensional ECQC witness

All logarithms in this module are natural logarithms.  A simultaneous change
of base scales both sides of the final strict inequality by the same positive
constant.  The physical Born-rule identification is proved in a separate module.
-/

namespace ECQC5

open scoped BigOperators

/-- Shannon entropy of a finite real-valued probability table.  As in mathlib,
`Real.log 0 = 0`, implementing the usual `0 log 0 = 0` convention. -/
noncomputable def shannon {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  - ∑ i, p i * Real.log (p i)

/-- Row marginal of a five-by-five joint outcome table. -/
def rowSums (P : Fin 5 → Fin 5 → ℝ) (i : Fin 5) : ℝ := ∑ j, P i j

/-- Column marginal of a five-by-five joint outcome table. -/
def colSums (P : Fin 5 → Fin 5 → ℝ) (j : Fin 5) : ℝ := ∑ i, P i j

/-- The ordinary Shannon mutual information of a joint outcome table. -/
noncomputable def classicalMI (P : Fin 5 → Fin 5 → ℝ) : ℝ :=
  shannon (rowSums P) + shannon (colSums P) -
    shannon (fun ij : Fin 5 × Fin 5 => P ij.1 ij.2)

/-- Every one of the six matched local measurements has this joint table. -/
noncomputable def tableZ (i j : Fin 5) : ℝ := if j = 2 * i then 1 / 5 else 0

/-- The equivalent linear-congruence description of the quadratic-basis table. -/
noncomputable def tableF (i j : Fin 5) : ℝ := if (i.val + 2 * j.val) % 5 = 0 then 1 / 5 else 0

theorem tableF_eq_tableZ : tableF = tableZ := by
  funext i j
  have h : ((i.val + 2 * j.val) % 5 = 0) ↔ j = 2 * i := by
    fin_cases i <;> fin_cases j <;> decide
  simp only [tableF, tableZ, h]

theorem tableZ_nonneg (i j : Fin 5) : 0 ≤ tableZ i j := by
  unfold tableZ
  split <;> norm_num

theorem tableZ_row (i : Fin 5) : rowSums tableZ i = 1 / 5 := by
  fin_cases i <;> norm_num [rowSums, tableZ, Fin.sum_univ_succ]

theorem tableZ_col (j : Fin 5) : colSums tableZ j = 1 / 5 := by
  rw [← tableF_eq_tableZ]
  fin_cases j <;> norm_num [colSums, tableF, Fin.sum_univ_succ]

theorem tableZ_normalized : (∑ i, ∑ j, tableZ i j) = 1 := by
  change (∑ i, rowSums tableZ i) = 1
  simp_rw [tableZ_row]
  norm_num

theorem uniform5_shannon : shannon (fun _ : Fin 5 => (1 : ℝ) / 5) = Real.log 5 := by
  norm_num [shannon, Fin.sum_univ_succ, Real.log_div]
  ring

theorem tableZ_joint_shannon :
    shannon (fun ij : Fin 5 × Fin 5 => tableZ ij.1 ij.2) = Real.log 5 := by
  norm_num [shannon, Fintype.sum_prod_type, Fin.sum_univ_succ, tableZ, Real.log_div]
  ring

theorem tableZ_classicalMI : classicalMI tableZ = Real.log 5 := by
  have hr : rowSums tableZ = fun _ : Fin 5 => (1 : ℝ) / 5 := funext tableZ_row
  have hc : colSums tableZ = fun _ : Fin 5 => (1 : ℝ) / 5 := funext tableZ_col
  rw [classicalMI, hr, hc, uniform5_shannon, tableZ_joint_shannon]
  ring

/-- `none` indexes the computational basis; `some a` indexes the quadratic
basis with parameter `a`.  Each of the six settings has the same table. -/
noncomputable def modelTable (_ : Option (Fin 5)) : Fin 5 → Fin 5 → ℝ := tableZ

theorem modelTable_classicalMI (b : Option (Fin 5)) :
    classicalMI (modelTable b) = Real.log 5 := tableZ_classicalMI

/-- The ECQC score for a selected collection of matched local measurements. -/
noncomputable def selectedScore (S : Finset (Option (Fin 5))) : ℝ :=
  ∑ b ∈ S, classicalMI (modelTable b)

theorem selectedScore_eq (S : Finset (Option (Fin 5))) (hS : S.card = 5) :
    selectedScore S = 5 * Real.log 5 := by
  unfold selectedScore
  simp_rw [modelTable_classicalMI]
  simp [hS]

theorem selectedScore_gt (S : Finset (Option (Fin 5))) (hS : S.card = 5) :
    2 * Real.log 5 < selectedScore S := by
  rw [selectedScore_eq S hS]
  have hlog : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- The strict violation also holds after converting natural logarithms to bits. -/
theorem selectedScore_bits_gt (S : Finset (Option (Fin 5))) (hS : S.card = 5) :
    (2 * Real.log 5) / Real.log 2 < selectedScore S / Real.log 2 := by
  exact div_lt_div_of_pos_right (selectedScore_gt S hS) (Real.log_pos (by norm_num))

/-- Every permitted five-setting selection strictly violates the proposed
budget `2 log 5`; therefore taking the minimum over selections cannot repair it. -/
theorem all_five_setting_selections_violate :
    ∀ S : Finset (Option (Fin 5)), S.card = 5 →
      selectedScore S = 5 * Real.log 5 ∧ 2 * Real.log 5 < selectedScore S := by
  intro S hS
  exact ⟨selectedScore_eq S hS, selectedScore_gt S hS⟩

/-- The selection domain is nonempty: there are six settings, so deleting
one leaves a permitted five-element selection. -/
theorem five_settings_exist : ∃ S : Finset (Option (Fin 5)), S.card = 5 := by
  refine ⟨Finset.univ.erase none, ?_⟩
  simp

/-- Existential formulation of failure of ECQC: there is no permissible
selection whose score is at most the state's quantum-information budget. -/
theorem no_five_setting_budget :
    ¬ ∃ S : Finset (Option (Fin 5)), S.card = 5 ∧ selectedScore S ≤ 2 * Real.log 5 := by
  rintro ⟨S, hS, hbound⟩
  exact (not_le_of_gt (selectedScore_gt S hS)) hbound

#print axioms ECQC5.five_settings_exist
#print axioms ECQC5.no_five_setting_budget
#print axioms ECQC5.tableF_eq_tableZ
#print axioms ECQC5.tableZ_nonneg
#print axioms ECQC5.tableZ_normalized
#print axioms ECQC5.tableZ_classicalMI
#print axioms ECQC5.all_five_setting_selections_violate

end ECQC5
