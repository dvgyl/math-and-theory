module
public import MilneDefs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Milne

/-- The squared three-setting steering bound at filter Bloch length r. -/
def steeringQuadratic (c r : ℝ) : ℝ :=
  (1-r^2)*(3-4*c)+(c+(1-c)*r)^2

def steeringDenominator (c : ℝ) : ℝ := 2-2*c-c^2

/-- Exact sharp squared F3 envelope, expressed without removable radicals. -/
def steeringEnvelopeSq (c : ℝ) : ℝ :=
  if c ≤ 2/3 then 1+(2-3*c)^2 / steeringDenominator c else 1

theorem steeringDenominator_pos {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3) :
    0 < steeringDenominator c := by
  have h := mul_nonneg hc0 (sub_nonneg.mpr hc)
  unfold steeringDenominator
  nlinarith

theorem steeringQuadratic_small {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3)
    (r : ℝ) : steeringQuadratic c r ≤ 1+(2-3*c)^2/steeringDenominator c := by
  have hd := steeringDenominator_pos hc0 hc
  have hid : steeringDenominator c + (2-3*c)^2 -
      steeringQuadratic c r * steeringDenominator c =
      (steeringDenominator c*r-c*(1-c))^2 := by
    unfold steeringDenominator steeringQuadratic
    ring
  have hn : steeringQuadratic c r * steeringDenominator c ≤
      steeringDenominator c + (2-3*c)^2 := by
    nlinarith [sq_nonneg (steeringDenominator c*r-c*(1-c))]
  have hdiv := (le_div_iff₀ hd).mpr hn
  convert hdiv using 1
  field_simp

theorem steeringQuadratic_large {c r : ℝ} (hc : 2/3 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : steeringQuadratic c r ≤ 1 := by
  have hc0 : 0 ≤ c := by linarith
  have hcs : c^2 ≤ c := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have h0 : 0 ≤ 4*c-2-c^2 := by nlinarith
  have h1 : 0 ≤ 6*c-4 := by linarith
  have hprod0 := mul_nonneg (sq_nonneg (1-r)) h0
  have hprod1 := mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr1)) h1
  have hid : 1-steeringQuadratic c r =
      (1-r)^2*(4*c-2-c^2)+r*(1-r)*(6*c-4) := by
    unfold steeringQuadratic
    ring
  linarith

theorem steeringQuadratic_le_envelope {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    steeringQuadratic c r ≤ steeringEnvelopeSq c := by
  unfold steeringEnvelopeSq
  split_ifs with h
  · exact steeringQuadratic_small hc0 h r
  · exact steeringQuadratic_large (le_of_not_ge h) hc1 hr0 hr1

theorem steeringEnvelopeSq_ge_one {c : ℝ} (hc0 : 0 ≤ c) :
    1 ≤ steeringEnvelopeSq c := by
  unfold steeringEnvelopeSq
  split_ifs with hc
  · have h := div_nonneg (sq_nonneg (2-3*c)) (le_of_lt (steeringDenominator_pos hc0 hc))
    linarith
  · exact le_rfl

theorem steeringEnvelopeSq_formula {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3) :
    steeringEnvelopeSq c = 2*(1-c)*(3-4*c)/steeringDenominator c := by
  rw [steeringEnvelopeSq, if_pos hc]
  have hd := ne_of_gt (steeringDenominator_pos hc0 hc)
  field_simp
  unfold steeringDenominator
  ring

theorem steering_vertex_in_unit_interval {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3) :
    0 ≤ c*(1-c)/steeringDenominator c ∧ c*(1-c)/steeringDenominator c ≤ 1 := by
  have hd := steeringDenominator_pos hc0 hc
  constructor
  · exact div_nonneg (mul_nonneg hc0 (by linarith)) (le_of_lt hd)
  · apply (div_le_iff₀ hd).mpr
    unfold steeringDenominator
    nlinarith

theorem steering_vertex_attains {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3) :
    steeringQuadratic c (c*(1-c)/steeringDenominator c) = steeringEnvelopeSq c := by
  rw [steeringEnvelopeSq, if_pos hc]
  have hd := ne_of_gt (steeringDenominator_pos hc0 hc)
  unfold steeringQuadratic
  field_simp
  unfold steeringDenominator
  ring

theorem steering_endpoint (c : ℝ) : steeringQuadratic c 1 = 1 := by
  unfold steeringQuadratic
  ring

theorem steeringEnvelopeSq_eq_one {c : ℝ} (hc : 2/3 ≤ c) :
    steeringEnvelopeSq c = 1 := by
  unfold steeringEnvelopeSq
  split_ifs with h
  · have he : c = 2/3 := le_antisymm h hc
    subst c
    norm_num [steeringDenominator]
  · rfl

theorem steeringEnvelopeSq_gt_one {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    1 < steeringEnvelopeSq c := by
  rw [steeringEnvelopeSq, if_pos (le_of_lt hc)]
  have hnum : 0 < (2-3*c)^2 := sq_pos_of_pos (by linarith)
  have h := div_pos hnum (steeringDenominator_pos hc0 (le_of_lt hc))
  linarith

theorem steering_vertex_lt_one {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    c*(1-c)/steeringDenominator c < 1 := by
  apply (div_lt_iff₀ (steeringDenominator_pos hc0 (le_of_lt hc))).mpr
  unfold steeringDenominator
  nlinarith

theorem chsh_filter_interpolation {c r2 x : ℝ} (hr0 : 0 ≤ r2) (hr1 : r2 ≤ 1)
    (hx : x ≤ 2*(1-c)) : (1-r2)*x+r2 ≤ max (2*(1-c)) 1 := by
  have h0 := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hr1)
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (2*(1-c)) 1)
    (sub_nonneg.mpr hr1)
  have h2 := mul_le_mul_of_nonneg_left (le_max_right (2*(1-c)) 1) hr0
  nlinarith

end Milne
