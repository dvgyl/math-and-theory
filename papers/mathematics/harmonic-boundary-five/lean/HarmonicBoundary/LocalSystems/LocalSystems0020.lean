import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace HarmonicBoundary.LocalSystems
private theorem zero_or_one (x : Int) (h : 0 ≤ x ∧ x ≤ 1) : x = 0 ∨ x = 1 := by omega

-- Local type [1, 1, 3, 3, 0, 0, 1, 1, 0, 4]; 3 mandatory and 6 optional profiles.
theorem local_type_0020_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0020_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 1, 0, 5]; 3 mandatory and 6 optional profiles.
theorem local_type_0021_infeasible
    (x0 x1 x2 x3 x4 x5 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (-1 : Int) * x5) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x5) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_3 : ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_4 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_5 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0021_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 1, 1, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0022_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
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
    rcases h_score_4_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0
  all_goals omega -splitDisjunctions

#print axioms local_type_0022_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 1, 2, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0023_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1))
    : False := by
  have h_certificate_1 : x3 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0 | h_path_1
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0 | h_path_1
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : x1 = 0 := by
    rcases h_score_4_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0 | h_path_1
  all_goals omega -splitDisjunctions

#print axioms local_type_0023_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 2, 0, 4]; 3 mandatory and 7 optional profiles.
theorem local_type_0024_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_3 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_5 : x1 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4 := by
    rcases h_degree_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0024_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 2, 0, 5]; 3 mandatory and 7 optional profiles.
theorem local_type_0025_infeasible
    (x0 x1 x2 x3 x4 x5 x6 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_bound_5 : 0 ≤ x5 ∧ x5 ≤ 1)
    (h_bound_6 : 0 ≤ x6 ∧ x6 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x4) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x4 + (1 : Int) * x5) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (-1 : Int) * x5) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x5) ≤ 0)
    (h_degree_5 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≥ 4)
    (h_score_5_0 : x2 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x3 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_1 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x4 + (-1 : Int) * x5 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_2 : x2 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3 + (1 : Int) * x4 + (-1 : Int) * x6) ≤ 0)
    (h_score_5_3 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x4 + (1 : Int) * x5 + (1 : Int) * x6) ≤ 0)
    (h_score_5_4 : x2 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x1 + (1 : Int) * x3 + (-1 : Int) * x4 + (1 : Int) * x6) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x6 = 1) ∨ (x0 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x5 = 1 ∧ x6 = 1) ∨ (x1 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨ (x2 = 1 ∧ x4 = 1 ∧ x6 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : ((1 : Int) * 1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_3 : x3 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((1 : Int) * 1 + (1 : Int) * x1 + (-1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_2 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_5 : x1 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0 := by
    rcases h_score_3_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_7 : x2 = 0 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_8 : x4 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_9 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 4 := by
    rcases h_degree_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0025_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 2, 1, 4]; 3 mandatory and 5 optional profiles.
theorem local_type_0026_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_3 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_3_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0026_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 2, 1, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0027_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x3) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x3 = 1 ∧ x4 = 1))
    : False := by
  have h_certificate_1 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_2 : ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0 := by
    rcases h_score_3_0 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  have h_certificate_3 : x2 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0 := by
    rcases h_score_3_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0027_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 1, 2, 2, 5]; 3 mandatory and 3 optional profiles.
theorem local_type_0028_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 1 := by
    apply Int.le_antisymm <;> omega -splitDisjunctions
  have h_certificate_4 : ((-1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≤ 0 := by
    rcases h_score_3_3 with h_zero | h_inequality
    · omega -splitDisjunctions
    · omega -splitDisjunctions
  omega -splitDisjunctions

#print axioms local_type_0028_infeasible

-- Local type [1, 1, 3, 3, 0, 0, 2, 0, 2, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0029_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    have h_certificate_2 : x2 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_3 : x1 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
    all_goals omega -splitDisjunctions
  ·
    have h_certificate_4 : x1 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    rcases zero_or_one x2 h_bound_2 with h_certificate_5 | h_certificate_5
    ·
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
      all_goals omega -splitDisjunctions
    ·
      have h_certificate_6 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
        rcases h_score_3_4 with h_zero | h_inequality
        · omega -splitDisjunctions
        · omega -splitDisjunctions
      have h_certificate_7 : x3 = 0 := by
        apply Int.le_antisymm <;> omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
      all_goals omega -splitDisjunctions

#print axioms local_type_0029_infeasible

-- Local type [1, 1, 3, 3, 0, 1, 1, 1, 1, 5]; 3 mandatory and 2 optional profiles.
theorem local_type_0030_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : False)
    : False := by
  exact h_two_paths

#print axioms local_type_0030_infeasible

-- Local type [1, 1, 3, 3, 0, 1, 1, 2, 2, 5]; 3 mandatory and 2 optional profiles.
theorem local_type_0031_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : False)
    : False := by
  exact h_two_paths

#print axioms local_type_0031_infeasible

-- Local type [1, 1, 3, 3, 0, 1, 2, 1, 2, 5]; 3 mandatory and 3 optional profiles.
theorem local_type_0032_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 0 := by
    rcases h_score_3_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0
  all_goals omega -splitDisjunctions

#print axioms local_type_0032_infeasible

-- Local type [1, 1, 3, 3, 0, 2, 2, 2, 2, 5]; 3 mandatory and 2 optional profiles.
theorem local_type_0033_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * 1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * 1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : False)
    : False := by
  exact h_two_paths

#print axioms local_type_0033_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 0, 0, 0, 5]; 3 mandatory and 2 optional profiles.
theorem local_type_0034_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : False)
    : False := by
  exact h_two_paths

#print axioms local_type_0034_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 0, 0, 1, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0035_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
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
  have h_certificate_3 : x1 = 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  have h_certificate_4 : x0 = 0 := by
    rcases h_degree_3 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0
  all_goals omega -splitDisjunctions

#print axioms local_type_0035_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 0, 1, 1, 5]; 3 mandatory and 2 optional profiles.
theorem local_type_0036_infeasible
    (x0 x1 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1) ≤ 0)
    (h_two_paths : False)
    : False := by
  exact h_two_paths

#print axioms local_type_0036_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 1, 0, 1, 5]; 3 mandatory and 4 optional profiles.
theorem local_type_0037_infeasible
    (x0 x1 x2 x3 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (-1 : Int) * x3) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (1 : Int) * x3) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
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
  have h_certificate_3 : x1 = 0 := by
    rcases h_score_4_4 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0
  all_goals omega -splitDisjunctions

#print axioms local_type_0037_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 1, 1, 2, 5]; 3 mandatory and 3 optional profiles.
theorem local_type_0038_infeasible
    (x0 x1 x2 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x2) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1))
    : False := by
  have h_certificate_1 : x2 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_2 : x1 = 1 := by
    apply Int.le_antisymm
    · omega -splitDisjunctions
    ·
      rcases h_two_paths with h_path_0
      all_goals omega -splitDisjunctions
  have h_certificate_3 : x0 = 0 := by
    rcases h_score_3_1 with h_zero | h_inequality
    · exact h_zero
    · exfalso; omega -splitDisjunctions
  rcases h_two_paths with h_path_0
  all_goals omega -splitDisjunctions

#print axioms local_type_0038_infeasible

-- Local type [1, 1, 3, 3, 1, 0, 2, 0, 2, 5]; 3 mandatory and 5 optional profiles.
theorem local_type_0039_infeasible
    (x0 x1 x2 x3 x4 : Int)
    (h_bound_0 : 0 ≤ x0 ∧ x0 ≤ 1)
    (h_bound_1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h_bound_2 : 0 ≤ x2 ∧ x2 ≤ 1)
    (h_bound_3 : 0 ≤ x3 ∧ x3 ≤ 1)
    (h_bound_4 : 0 ≤ x4 ∧ x4 ≤ 1)
    (h_degree_0 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x1) ≥ 2)
    (h_degree_1 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_2 : ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2) ≥ 2)
    (h_degree_3 : x0 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x2 + (1 : Int) * x3) ≥ 4)
    (h_score_3_0 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_1 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_2 : x0 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0)
    (h_score_3_3 : x0 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * 1 + (1 : Int) * x1 + (1 : Int) * x3) ≤ 0)
    (h_score_3_4 : x0 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3) ≤ 0)
    (h_degree_4 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≥ 4)
    (h_score_4_0 : x1 = 0 ∨ ((1 : Int) * 1 + (-1 : Int) * x2 + (-1 : Int) * x3 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_1 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_2 : x1 = 0 ∨ ((1 : Int) * 1 + (1 : Int) * x0 + (1 : Int) * x2 + (-1 : Int) * x4) ≤ 0)
    (h_score_4_3 : x1 = 0 ∨ ((-1 : Int) * 1 + (-1 : Int) * x0 + (-1 : Int) * x2 + (1 : Int) * x4) ≤ 0)
    (h_score_4_4 : x1 = 0 ∨ ((-1 : Int) * 1 + (1 : Int) * x2 + (1 : Int) * x3 + (1 : Int) * x4) ≤ 0)
    (h_two_paths : (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x2 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x1 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨ (x0 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x3 = 1) ∨ (x1 = 1 ∧ x2 = 1 ∧ x4 = 1))
    : False := by
  rcases zero_or_one x0 h_bound_0 with h_certificate_1 | h_certificate_1
  ·
    rcases zero_or_one x2 h_bound_2 with h_certificate_2 | h_certificate_2
    ·
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
      all_goals omega -splitDisjunctions
    ·
      have h_certificate_3 : x1 = 0 := by
        rcases h_score_4_1 with h_zero | h_inequality
        · exact h_zero
        · exfalso; omega -splitDisjunctions
      rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
      all_goals omega -splitDisjunctions
  ·
    have h_certificate_4 : x1 = 0 := by
      rcases h_score_4_1 with h_zero | h_inequality
      · exact h_zero
      · exfalso; omega -splitDisjunctions
    have h_certificate_5 : ((1 : Int) * 1 + (-1 : Int) * x1 + (-1 : Int) * x3) ≤ 0 := by
      rcases h_score_3_1 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_6 : x3 = 1 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    have h_certificate_7 : ((-1 : Int) * 1 + (1 : Int) * x3 + (1 : Int) * x2) ≤ 0 := by
      rcases h_score_3_4 with h_zero | h_inequality
      · omega -splitDisjunctions
      · omega -splitDisjunctions
    have h_certificate_8 : x2 = 0 := by
      apply Int.le_antisymm <;> omega -splitDisjunctions
    rcases h_two_paths with h_path_0 | h_path_1 | h_path_2 | h_path_3 | h_path_4 | h_path_5
    all_goals omega -splitDisjunctions

#print axioms local_type_0039_infeasible


end HarmonicBoundary.LocalSystems
