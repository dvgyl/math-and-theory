import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [1, 3, 3, 3, 0, 0, 1, 5, 4, 5]; 2 mandatory and 4 optional profiles.
theorem local_type_0240_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0240_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 1, 5, 5, 5]; 2 mandatory and 4 optional profiles.
theorem local_type_0241_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0241_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 0, 5, 5]; 2 mandatory and 8 optional profiles.
theorem local_type_0242_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x6) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x7) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x7) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_4 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25
    all_goals omega -splitDisjunctions
  ·
    have h_certificate_5 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases zero_or_one x3 h_bound_3 with h_certificate_7 | h_certificate_7
    ·
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25
      all_goals omega -splitDisjunctions
    ·
      have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_9 : x5 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_10 : x4 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25
      all_goals omega -splitDisjunctions

#print axioms local_type_0242_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 1, 5, 5]; 2 mandatory and 8 optional profiles.
theorem local_type_0243_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((1 : Int) * x2 + (1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x7) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((1 : Int) * x1 + (1 : Int) * x4 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x7) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_4 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
    all_goals omega -splitDisjunctions
  ·
    have h_certificate_5 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases zero_or_one x3 h_bound_3 with h_certificate_7 | h_certificate_7
    ·
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
      all_goals omega -splitDisjunctions
    ·
      have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_9 : x5 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_10 : x4 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
      all_goals omega -splitDisjunctions

#print axioms local_type_0243_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 2, 5, 5]; 2 mandatory and 6 optional profiles.
theorem local_type_0244_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_8 | h_certificate_8
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_13 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_14 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_16 : x2 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions

#print axioms local_type_0244_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 3, 5, 5]; 2 mandatory and 6 optional profiles.
theorem local_type_0245_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_8 | h_certificate_8
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_13 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_14 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_16 : x2 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions

#print axioms local_type_0245_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 4, 5, 5]; 2 mandatory and 5 optional profiles.
theorem local_type_0246_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_10 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0246_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 3, 3]; 2 mandatory and 5 optional profiles.
theorem local_type_0247_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_10 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0247_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 3, 4]; 2 mandatory and 6 optional profiles.
theorem local_type_0248_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_8 | h_certificate_8
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_13 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0 := by
        rcases h_score_3_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_14 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_16 : x2 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_18 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_19 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions

#print axioms local_type_0248_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 3, 5]; 2 mandatory and 6 optional profiles.
theorem local_type_0249_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_8 | h_certificate_8
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_2_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_13 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0 := by
        rcases h_score_3_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_14 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_16 : x2 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x5 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_18 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_19 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
        rcases h_degree_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions

#print axioms local_type_0249_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 4, 4]; 2 mandatory and 5 optional profiles.
theorem local_type_0250_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_10 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0250_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 4, 5]; 2 mandatory and 5 optional profiles.
theorem local_type_0251_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_10 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0251_infeasible

-- Local type [1, 3, 3, 3, 0, 0, 2, 5, 5, 5]; 2 mandatory and 5 optional profiles.
theorem local_type_0252_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_8 : x1 = 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_10 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_11 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0252_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 0, 5, 5]; 2 mandatory and 8 optional profiles.
theorem local_type_0253_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x7) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x4 + (1 : Int) * x7) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x4 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x6 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_3_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_4 : x6 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_5 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : x2 = 0 := by
      rcases h_degree_4 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19
    all_goals omega -splitDisjunctions
  ·
    have h_certificate_7 : x1 = 0 := by
      rcases h_score_3_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_8 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19
    all_goals omega -splitDisjunctions

#print axioms local_type_0253_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 1, 5, 5]; 2 mandatory and 6 optional profiles.
theorem local_type_0254_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
  all_goals omega -splitDisjunctions

#print axioms local_type_0254_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 2, 5, 5]; 2 mandatory and 5 optional profiles.
theorem local_type_0255_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2
  all_goals omega -splitDisjunctions

#print axioms local_type_0255_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 3, 5, 5]; 2 mandatory and 4 optional profiles.
theorem local_type_0256_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
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
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0256_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 4, 5, 5]; 2 mandatory and 4 optional profiles.
theorem local_type_0257_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0257_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 1, 5, 5, 5]; 2 mandatory and 4 optional profiles.
theorem local_type_0258_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0258_infeasible

-- Local type [1, 3, 3, 3, 0, 1, 2, 0, 5, 5]; 2 mandatory and 8 optional profiles.
theorem local_type_0259_infeasible
    (x0 x1 x2 x3 x4 x5 x6 x7 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_bound_7 : 0 ≤ x7 ∧ x7 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 2)
    (h_degree_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_2_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_2_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_2_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_3 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≥ 4)
    (h_score_3_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x6) ≤ 0)
    (h_score_3_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x6) ≤ 0)
    (h_score_3_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_degree_4 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x7) ≥ 4)
    (h_score_4_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x5 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3 + (1 : Int) * x7) ≤ 0)
    (h_score_4_3 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0)
    (h_score_4_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x7) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x7 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x6 = 1 ∧ x7 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x7 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x7 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_2 | h_certificate_2
    ·
      have h_certificate_3 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5 + (1 : Int) * x7) ≥ 4 := by
        rcases h_degree_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_5 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : x7 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_8 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (-1 : Int) * x7) ≤ 0 := by
        rcases h_score_4_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (-1 : Int) * x6) ≤ 0 := by
        rcases h_score_3_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x6 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x6 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_3_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_12 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_13 : ((-1 : Int) * 1 + (1 : Int) * x6 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_14 : x4 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_15 : x2 = 0 := by
        rcases h_degree_4 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29 | h_path_30
      all_goals omega -splitDisjunctions
  ·
    have h_certificate_16 : x1 = 0 := by
      rcases h_score_3_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_17 : x2 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_18 : ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0 := by
      rcases h_score_2_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_19 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_20 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0 := by
      rcases h_score_2_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_21 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_22 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29 | h_path_30
    all_goals omega -splitDisjunctions

#print axioms local_type_0259_infeasible


end HarmonicBoundary.LocalSystems
