import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [2, 2, 3, 3, 3, 0, 2, 0, 3, 5]; 3 mandatory and 7 optional profiles.
theorem local_type_0540_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : ((-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x5) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_12 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : ((-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_14 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_15 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_16 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_17 : ((1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x0 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0540_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 2, 1, 3, 5]; 3 mandatory and 6 optional profiles.
theorem local_type_0541_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : ((1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_11 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : x0 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_14 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14
    all_goals omega -splitDisjunctions

#print axioms local_type_0541_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 3, 0, 3, 5]; 3 mandatory and 7 optional profiles.
theorem local_type_0542_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : ((-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_12 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_14 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_15 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_16 : ((1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x0 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0542_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 3, 0, 4, 5]; 3 mandatory and 7 optional profiles.
theorem local_type_0543_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : ((-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_12 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_14 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_15 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_16 : ((1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x0 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0543_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 3, 1, 4, 5]; 3 mandatory and 6 optional profiles.
theorem local_type_0544_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_9 : x2 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_10 : ((1 : Int) * 1 + (-1 : Int) * x2 + (1 : Int) * x0 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_11 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : x0 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0544_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 4, 0, 4, 5]; 3 mandatory and 7 optional profiles.
theorem local_type_0545_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x0 = 0 := by
    rcases h_score_3_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0545_infeasible

-- Local type [2, 2, 3, 3, 3, 0, 4, 1, 4, 5]; 3 mandatory and 6 optional profiles.
theorem local_type_0546_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x0 = 0 := by
    rcases h_score_3_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0546_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 1, 1, 1, 5]; 3 mandatory and 3 optional profiles.
theorem local_type_0547_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0547_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 1, 2, 2, 5]; 3 mandatory and 3 optional profiles.
theorem local_type_0548_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0548_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 2, 1, 2, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0549_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0549_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 2, 1, 3, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0550_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x4) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_6 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_8 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0550_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 2, 2, 3, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0551_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0551_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 3, 1, 3, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0552_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0552_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 3, 1, 4, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0553_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0553_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 3, 2, 4, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0554_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0554_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 4, 1, 4, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0555_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_3_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0555_infeasible

-- Local type [2, 2, 3, 3, 3, 1, 4, 2, 4, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0556_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0556_infeasible

-- Local type [2, 3, 3, 3, 0, 0, 3, 0, 5, 5]; 2 mandatory and 10 optional profiles.
theorem local_type_0557_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_bound_8 : 0 ≤ x8 ∧ x8 ≤ 1)
    (h_bound_9 : 0 ≤ x9 ∧ x9 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x8) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x8) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x8) ≤ 0)
    (h_degree_5 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x7 + (1 : Int) * x9) ≥ 4)
    (h_score_5_0 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x7 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_1 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_2 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_3 : x3 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5 + (1 : Int) * x9) ≤ 0)
    (h_score_5_4 : x3 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x7 + (1 : Int) * x9) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x9 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x7 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x8 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x8 = 1 ∧ x9 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x3 h_bound_3 with h_certificate_2 | h_certificate_2
    ·
      have h_certificate_3 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_4 : x0 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x8) ≥ 4 := by
        rcases h_degree_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : x6 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_8 : x8 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x8) ≤ 0 := by
        rcases h_score_4_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_10 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x9 + (1 : Int) * x7 + (1 : Int) * x5) ≥ 4 := by
        rcases h_degree_5 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_11 : x9 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : x7 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_13 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_14 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x9 + (1 : Int) * x5) ≤ 0 := by
        rcases h_score_5_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
  ·
    have h_certificate_15 : x3 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_16 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_17 : x0 = 0 := by
      rcases h_score_2_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29 | h_path_30 | h_path_31 | h_path_32 | h_path_33 | h_path_34 | h_path_35 | h_path_36 | h_path_37 | h_path_38 | h_path_39 | h_path_40 | h_path_41 | h_path_42 | h_path_43 | h_path_44 | h_path_45 | h_path_46 | h_path_47 | h_path_48 | h_path_49 | h_path_50
    all_goals omega -splitDisjunctions

#print axioms local_type_0557_infeasible

-- Local type [2, 3, 3, 3, 0, 0, 3, 1, 5, 5]; 2 mandatory and 10 optional profiles.
theorem local_type_0558_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_bound_8 : 0 ≤ x8 ∧ x8 ≤ 1)
    (h_bound_9 : 0 ≤ x9 ∧ x9 ≤ 1)
    (h_degree_0 : ((1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x7) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7 + (1 : Int) * x8) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x7 + (1 : Int) * x8) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((1 : Int) * x3 + (1 : Int) * x7 + (-1 : Int) * x8) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7 + (1 : Int) * x8) ≤ 0)
    (h_degree_5 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7 + (1 : Int) * x9) ≥ 4)
    (h_score_5_0 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_1 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_2 : x3 = 0 ∨ ((1 : Int) * x2 + (1 : Int) * x6 + (-1 : Int) * x9) ≤ 0)
    (h_score_5_3 : x3 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x5 + (-1 : Int) * x6 + (1 : Int) * x9) ≤ 0)
    (h_score_5_4 : x3 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7 + (1 : Int) * x9) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x8 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x9 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x7 = 1 ∧ x8 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x9 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x8 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x8 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x6 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x8 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x9 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x8 = 1 ∧ x9 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x3 h_bound_3 with h_certificate_2 | h_certificate_2
    ·
      have h_certificate_3 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_4 : x0 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (-1 : Int) * x8) ≤ 0 := by
        rcases h_score_4_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_6 : x8 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : x5 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * x7 + (1 : Int) * x6 + (1 : Int) * x5 + (1 : Int) * x8) ≤ 0 := by
        rcases h_score_4_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_9 : x7 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_10 : x6 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_12 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x9 + (1 : Int) * x5) ≤ 0 := by
        rcases h_score_5_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_13 : x9 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_14 : x5 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : ((-1 : Int) * 1 + (1 : Int) * x9 + (1 : Int) * x7 + (1 : Int) * x6 + (1 : Int) * x5) ≤ 0 := by
        rcases h_score_5_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_16 : x7 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_17 : x6 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_18 : x2 = 0 := by
        rcases h_degree_4 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      have h_certificate_19 : x0 = 0 := by
        rcases h_degree_2 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29 | h_path_30 | h_path_31 | h_path_32 | h_path_33 | h_path_34 | h_path_35 | h_path_36 | h_path_37 | h_path_38 | h_path_39 | h_path_40 | h_path_41 | h_path_42 | h_path_43 | h_path_44 | h_path_45 | h_path_46 | h_path_47 | h_path_48 | h_path_49 | h_path_50 | h_path_51 | h_path_52 | h_path_53 | h_path_54 | h_path_55 | h_path_56 | h_path_57 | h_path_58 | h_path_59 | h_path_60
      all_goals omega -splitDisjunctions
  ·
    have h_certificate_20 : x3 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_21 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_22 : x0 = 0 := by
      rcases h_score_2_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29 | h_path_30 | h_path_31 | h_path_32 | h_path_33 | h_path_34 | h_path_35 | h_path_36 | h_path_37 | h_path_38 | h_path_39 | h_path_40 | h_path_41 | h_path_42 | h_path_43 | h_path_44 | h_path_45 | h_path_46 | h_path_47 | h_path_48 | h_path_49 | h_path_50 | h_path_51 | h_path_52 | h_path_53 | h_path_54 | h_path_55 | h_path_56 | h_path_57 | h_path_58 | h_path_59 | h_path_60
    all_goals omega -splitDisjunctions

#print axioms local_type_0558_infeasible

-- Local type [2, 3, 3, 3, 0, 0, 3, 2, 5, 5]; 2 mandatory and 8 optional profiles.
theorem local_type_0559_infeasible
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
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (1 : Int) * x6 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4 + (-1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x1 h_bound_1 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x0 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_2_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x0 = 0 := by
      rcases h_score_2_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x7 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_11 : x7 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_13 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_14 : ((-1 : Int) * 1 + (1 : Int) * x7 + (1 : Int) * x5 + (1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0559_infeasible


end HarmonicBoundary.LocalSystems
