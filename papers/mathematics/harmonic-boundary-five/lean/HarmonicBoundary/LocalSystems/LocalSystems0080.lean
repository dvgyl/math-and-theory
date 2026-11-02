import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [1, 2, 2, 3, 0, 1, 1, 1, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0080_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3
  all_goals omega -splitDisjunctions

#print axioms local_type_0080_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 1, 4, 3]; 4 mandatory and 4 optional profiles.
theorem local_type_0081_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3
  all_goals omega -splitDisjunctions

#print axioms local_type_0081_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 1, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0082_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3
  all_goals omega -splitDisjunctions

#print axioms local_type_0082_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 2, 3, 4]; 4 mandatory and 3 optional profiles.
theorem local_type_0083_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1
  all_goals omega -splitDisjunctions

#print axioms local_type_0083_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 2, 4, 3]; 4 mandatory and 3 optional profiles.
theorem local_type_0084_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1
  all_goals omega -splitDisjunctions

#print axioms local_type_0084_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 2, 4, 4]; 4 mandatory and 3 optional profiles.
theorem local_type_0085_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1
  all_goals omega -splitDisjunctions

#print axioms local_type_0085_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 1, 3, 4, 4]; 4 mandatory and 2 optional profiles.
theorem local_type_0086_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 0 := by
    rcases h_score_5_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4 := by
    rcases h_degree_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0086_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 0, 3, 4]; 4 mandatory and 6 optional profiles.
theorem local_type_0087_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_2 | h_certificate_2
    ·
      have h_certificate_3 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4 := by
        rcases h_degree_6 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_5 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_6_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_5_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_9 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_10 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_5_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_11 : x4 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : x2 = 0 := by
        rcases h_degree_6 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
      all_goals omega -splitDisjunctions
  ·
    have h_certificate_13 : x1 = 0 := by
      rcases h_score_5_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_14 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_15 : ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_16 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_18 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_19 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
    all_goals omega -splitDisjunctions

#print axioms local_type_0087_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 0, 4, 4]; 4 mandatory and 6 optional profiles.
theorem local_type_0088_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x2 + (-1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((1 : Int) * x1 + (-1 : Int) * x2 + (1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x1 h_bound_1 with h_certificate_2 | h_certificate_2
    ·
      have h_certificate_3 : x2 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x5) ≥ 4 := by
        rcases h_degree_6 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_5 : x3 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_6_1 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_5_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_9 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_10 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3) ≤ 0 := by
        rcases h_score_5_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_11 : x4 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : x2 = 0 := by
        rcases h_degree_6 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
      all_goals omega -splitDisjunctions
  ·
    have h_certificate_13 : x1 = 0 := by
      rcases h_score_5_2 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_14 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_15 : ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_16 : x5 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_17 : ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_18 : x4 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_19 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7 | h_path_8 | h_path_9 | h_path_10 | h_path_11 | h_path_12 | h_path_13 | h_path_14 | h_path_15 | h_path_16 | h_path_17 | h_path_18 | h_path_19 | h_path_20 | h_path_21 | h_path_22 | h_path_23 | h_path_24 | h_path_25 | h_path_26 | h_path_27 | h_path_28 | h_path_29
    all_goals omega -splitDisjunctions

#print axioms local_type_0088_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 1, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0089_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_8 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_9 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : x1 = 0 := by
      rcases h_degree_5 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7
    all_goals omega -splitDisjunctions

#print axioms local_type_0089_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 1, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0090_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_5 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_8 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_9 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : x1 = 0 := by
      rcases h_degree_5 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7
    all_goals omega -splitDisjunctions

#print axioms local_type_0090_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 2, 3, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0091_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_5 : x1 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_7 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7
    all_goals omega -splitDisjunctions

#print axioms local_type_0091_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 2, 4, 4]; 4 mandatory and 4 optional profiles.
theorem local_type_0092_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x1 = 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6 | h_path_7
  all_goals omega -splitDisjunctions

#print axioms local_type_0092_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 3, 3, 4]; 4 mandatory and 3 optional profiles.
theorem local_type_0093_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_4 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_5 : x1 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_7 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_8 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0093_infeasible

-- Local type [1, 2, 2, 3, 0, 1, 2, 3, 4, 4]; 4 mandatory and 3 optional profiles.
theorem local_type_0094_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x1 = 0 := by
    rcases h_score_5_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_2 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4 := by
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

#print axioms local_type_0094_infeasible

-- Local type [1, 2, 2, 3, 0, 2, 0, 0, 3, 2]; 4 mandatory and 6 optional profiles.
theorem local_type_0095_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_7 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x5) ≥ 4)
    (h_score_7_0 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_1 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_2 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_7_3 : x3 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_4 : x3 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x5 = 1) ∨ (x3 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x3 = 0 := by
    rcases h_score_7_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases zero_or_one x0 h_bound_0 with h_certificate_2 | h_certificate_2
  ·
    rcases zero_or_one x2 h_bound_2 with h_certificate_3 | h_certificate_3
    ·
      have h_certificate_4 : x1 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
        rcases h_degree_5 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0 := by
        rcases h_score_5_3 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x1 + (1 : Int) * x0 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
        rcases h_degree_6 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x1 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_13 : ((-1 : Int) * x3 + (1 : Int) * x1 + (-1 : Int) * x0 + (1 : Int) * x4) ≤ 0 := by
        rcases h_score_6_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
  ·
    have h_certificate_14 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_15 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_16 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_4_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0095_infeasible

-- Local type [1, 2, 2, 3, 0, 2, 0, 0, 4, 1]; 4 mandatory and 4 optional profiles.
theorem local_type_0096_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x2 = 1 ∧ x3 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 0 := by
      rcases h_degree_6 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_3 : x1 = 0 := by
      rcases h_degree_5 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5 | h_path_6
    all_goals omega -splitDisjunctions
  ·
    have h_certificate_4 : x2 = 0 := by
      rcases h_score_6_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_5 : x1 = 0 := by
      rcases h_degree_5 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0096_infeasible

-- Local type [1, 2, 2, 3, 0, 2, 0, 0, 4, 2]; 4 mandatory and 6 optional profiles.
theorem local_type_0097_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_6 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_6_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_6_2 : x2 = 0 ∨ ((-1 : Int) * x0 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_6_3 : x2 = 0 ∨ ((1 : Int) * x0 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_6_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_degree_7 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x5) ≥ 4)
    (h_score_7_0 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_1 : x3 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_2 : x3 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_score_7_3 : x3 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_7_4 : x3 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x5 = 1) ∨ (x3 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x3 = 0 := by
    rcases h_score_7_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases zero_or_one x0 h_bound_0 with h_certificate_2 | h_certificate_2
  ·
    rcases zero_or_one x2 h_bound_2 with h_certificate_3 | h_certificate_3
    ·
      have h_certificate_4 : x1 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
        rcases h_degree_5 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_6 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_7 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0 := by
        rcases h_score_5_3 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
    ·
      have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x1 + (1 : Int) * x0 + (1 : Int) * x5 + (1 : Int) * x4) ≥ 4 := by
        rcases h_degree_6 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_10 : x1 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_11 : x5 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_12 : x4 = 1 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      have h_certificate_13 : ((-1 : Int) * x3 + (1 : Int) * x1 + (-1 : Int) * x0 + (1 : Int) * x4) ≤ 0 := by
        rcases h_score_6_2 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      omega -splitDisjunctions
  ·
    have h_certificate_14 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_15 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_16 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_4_2 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0097_infeasible

-- Local type [1, 2, 2, 3, 0, 2, 2, 0, 3, 3]; 4 mandatory and 5 optional profiles.
theorem local_type_0098_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x4 = 1) ∨ (x1 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_4 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : x1 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_9 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : ((1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_11 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_13 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_14 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0098_infeasible

-- Local type [1, 2, 2, 3, 0, 2, 2, 0, 3, 4]; 4 mandatory and 5 optional profiles.
theorem local_type_0099_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 2)
    (h_degree_4 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4)
    (h_score_5_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_5_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_2 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2) ≤ 0)
    (h_score_5_3 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0)
    (h_score_5_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x4 = 1) ∨ (x1 = 1) ∨ (x1 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x1 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_5 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_4 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_5 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_6 : ((1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions
  ·
    have h_certificate_7 : x1 = 0 := by
      rcases h_score_5_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_8 : ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_9 : x4 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_10 : ((1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_3 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_11 : x3 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_12 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0 := by
      rcases h_score_4_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_13 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_14 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4 := by
      rcases h_degree_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    omega -splitDisjunctions

#print axioms local_type_0099_infeasible


end HarmonicBoundary.LocalSystems
