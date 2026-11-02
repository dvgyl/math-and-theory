import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [2, 2, 2, 3, 0, 1, 4, 3, 1, 2]; 4 mandatory and 4 optional profiles.
theorem local_type_0340_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_5 : x0 = 0 := by
      rcases h_score_4_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
    all_goals omega -splitDisjunctions

#print axioms local_type_0340_infeasible

-- Local type [2, 2, 2, 3, 0, 1, 4, 3, 2, 3]; 4 mandatory and 5 optional profiles.
theorem local_type_0341_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_6 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_8 : x0 = 0 := by
      rcases h_score_4_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11
    all_goals omega -splitDisjunctions

#print axioms local_type_0341_infeasible

-- Local type [2, 2, 2, 3, 0, 1, 4, 3, 3, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0342_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_6 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_5_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_9 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x0 = 0 := by
      rcases h_degree_4 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11
    all_goals omega -splitDisjunctions

#print axioms local_type_0342_infeasible

-- Local type [2, 2, 2, 3, 0, 1, 4, 3, 4, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0343_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x2 = 0 := by
    rcases h_score_6_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0343_infeasible

-- Local type [2, 2, 2, 3, 0, 2, 3, 2, 3, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0344_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x2 = 0 := by
    rcases h_score_6_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x0 = 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11
  all_goals omega -splitDisjunctions

#print axioms local_type_0344_infeasible

-- Local type [2, 2, 2, 3, 0, 2, 3, 2, 4, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0345_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x2 = 0 := by
    rcases h_score_6_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x0 = 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11
  all_goals omega -splitDisjunctions

#print axioms local_type_0345_infeasible

-- Local type [2, 2, 2, 3, 0, 2, 4, 2, 4, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0346_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x2 = 0 := by
    rcases h_score_6_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x0 = 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11
  all_goals omega -splitDisjunctions

#print axioms local_type_0346_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 3, 2, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0347_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0347_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 3, 2, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0348_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0348_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 3, 3, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0349_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0349_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 3, 3, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0350_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0350_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 2, 3, 3]; 4 mandatory and 4 optional profiles.
theorem local_type_0351_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0351_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 2, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0352_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0352_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 2, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0353_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0353_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 3, 2, 2]; 4 mandatory and 3 optional profiles.
theorem local_type_0354_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0354_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 3, 2, 3]; 4 mandatory and 4 optional profiles.
theorem local_type_0355_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0355_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 3, 3, 3]; 4 mandatory and 4 optional profiles.
theorem local_type_0356_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0356_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 3, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0357_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0357_infeasible

-- Local type [2, 2, 2, 3, 1, 1, 4, 3, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0358_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0358_infeasible

-- Local type [2, 2, 2, 3, 1, 2, 3, 2, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0359_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0359_infeasible


end HarmonicBoundary.LocalSystems
