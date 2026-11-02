import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [3, 3, 3, 3, 0, 4, 5, 5, 5, 5]; 1 mandatory and 8 optional profiles.
theorem local_type_0800_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_degree_3 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_3_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_score_3_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_3_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x7 + (1 : Int) * x6 + (1 : Int) * x5) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x7 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x7 + (1 : Int) * x5) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : x0 = 0 := by
      rcases h_score_1_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19
    all_goals omega -splitDisjunctions

#print axioms local_type_0800_infeasible

-- Local type [3, 3, 3, 3, 0, 5, 5, 5, 5, 5]; 1 mandatory and 8 optional profiles.
theorem local_type_0801_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_degree_3 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_3_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_score_3_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_3_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x7 + (1 : Int) * x6 + (1 : Int) * x5) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x7 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x7 + (1 : Int) * x5) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : x0 = 0 := by
      rcases h_score_1_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19
    all_goals omega -splitDisjunctions

#print axioms local_type_0801_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 2, 5, 5]; 1 mandatory and 7 optional profiles.
theorem local_type_0802_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x6 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x3) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_9 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_10 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_11 : ((-1 : Int) * 1 + (1 : Int) * x6 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0802_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 3, 5, 5]; 1 mandatory and 7 optional profiles.
theorem local_type_0803_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_9 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_10 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_11 : ((-1 : Int) * 1 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0803_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 4, 5, 5]; 1 mandatory and 6 optional profiles.
theorem local_type_0804_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0804_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 1, 1]; 1 mandatory and 4 optional profiles.
theorem local_type_0805_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0805_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 2, 2]; 1 mandatory and 5 optional profiles.
theorem local_type_0806_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0806_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 2, 3]; 1 mandatory and 7 optional profiles.
theorem local_type_0807_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_8 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x6 + (1 : Int) * x5) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_10 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_11 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_12 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0807_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 2, 4]; 1 mandatory and 8 optional profiles.
theorem local_type_0808_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x7 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_8 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0808_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 2, 5]; 1 mandatory and 8 optional profiles.
theorem local_type_0809_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x7 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_8 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0809_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 3, 3]; 1 mandatory and 6 optional profiles.
theorem local_type_0810_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0810_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 3, 4]; 1 mandatory and 7 optional profiles.
theorem local_type_0811_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x6 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_9 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_10 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_11 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0811_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 3, 5]; 1 mandatory and 7 optional profiles.
theorem local_type_0812_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_1_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x6 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_9 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_10 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_11 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0812_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 4, 4]; 1 mandatory and 6 optional profiles.
theorem local_type_0813_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0813_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 4, 5]; 1 mandatory and 6 optional profiles.
theorem local_type_0814_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0814_infeasible

-- Local type [3, 3, 3, 3, 1, 1, 5, 5, 5, 5]; 1 mandatory and 6 optional profiles.
theorem local_type_0815_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0815_infeasible

-- Local type [3, 3, 3, 3, 1, 2, 5, 2, 5, 5]; 1 mandatory and 7 optional profiles.
theorem local_type_0816_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x6 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x6) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x5 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0816_infeasible

-- Local type [3, 3, 3, 3, 1, 2, 5, 3, 5, 5]; 1 mandatory and 6 optional profiles.
theorem local_type_0817_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0817_infeasible

-- Local type [3, 3, 3, 3, 1, 2, 5, 4, 5, 5]; 1 mandatory and 6 optional profiles.
theorem local_type_0818_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4) ≤ 0 := by
    rcases h_score_2_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0818_infeasible

-- Local type [3, 3, 3, 3, 1, 2, 5, 5, 2, 3]; 1 mandatory and 6 optional profiles.
theorem local_type_0819_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_1_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_1_2 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_1_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0 := by
    rcases h_score_2_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x5 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0 := by
    rcases h_score_2_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x4 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
    rcases h_degree_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0819_infeasible


end HarmonicBoundary.LocalSystems
