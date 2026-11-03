import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Exact scalar completion used in the sharp conditional-purity theorem.
The physical block-matrix bound and cluster-set argument are proved in the
manuscript; this module certifies the scalar maximum, its physical vertex,
and the universal endpoint bounds without assuming an optimal certificate. -/

noncomputable section
namespace FilteredF3

def conditionalDenominator (r : ℝ) : ℝ := 3 + 6*r - r^2
def conditionalVertex (r : ℝ) : ℝ := (1+3*r) / conditionalDenominator r
def conditionalCapSq (r : ℝ) : ℝ := 1 + (1+3*r)^2 / conditionalDenominator r
def conditionalParabola (r t : ℝ) : ℝ :=
  1 + (2+6*r)*t - conditionalDenominator r*t^2

theorem conditional_denominator_positive (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < conditionalDenominator r := by
  unfold conditionalDenominator
  have hr2 : r^2 ≤ 1 := by nlinarith
  nlinarith

theorem conditional_exact_square (r t : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    conditionalCapSq r - conditionalParabola r t =
      conditionalDenominator r * (t-conditionalVertex r)^2 := by
  have hd := ne_of_gt (conditional_denominator_positive r hr0 hr1)
  unfold conditionalCapSq conditionalParabola conditionalVertex
  field_simp
  unfold conditionalDenominator
  ring

theorem conditional_cap_global (r t : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    conditionalParabola r t ≤ conditionalCapSq r := by
  have he := conditional_exact_square r t hr0 hr1
  have hn := mul_nonneg (le_of_lt (conditional_denominator_positive r hr0 hr1))
    (sq_nonneg (t-conditionalVertex r))
  linarith

theorem conditional_cap_attained (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    conditionalParabola r (conditionalVertex r) = conditionalCapSq r := by
  have he := conditional_exact_square r (conditionalVertex r) hr0 hr1
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at he
  linarith

theorem conditional_vertex_physical (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < conditionalVertex r ∧ conditionalVertex r < 1 := by
  have hd := conditional_denominator_positive r hr0 hr1
  unfold conditionalVertex
  constructor
  · exact div_pos (by linarith) hd
  · apply (div_lt_iff₀ hd).mpr
    unfold conditionalDenominator
    have hr2 : r^2 ≤ 1 := by nlinarith
    nlinarith

theorem conditional_cap_bounds (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (4:ℝ)/3 ≤ conditionalCapSq r ∧ conditionalCapSq r ≤ 3 := by
  have hd := conditional_denominator_positive r hr0 hr1
  have hlo : (1:ℝ)/3 ≤ (1+3*r)^2 / conditionalDenominator r := by
    apply (le_div_iff₀ hd).mpr
    unfold conditionalDenominator
    nlinarith [sq_nonneg r]
  have hhi : (1+3*r)^2 / conditionalDenominator r ≤ 2 := by
    apply (div_le_iff₀ hd).mpr
    unfold conditionalDenominator
    have hp := mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ 11*r+5 by linarith)
    nlinarith
  unfold conditionalCapSq
  constructor <;> linarith

theorem conditional_cap_isGreatest (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsGreatest {v : ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ conditionalParabola r t = v}
      (conditionalCapSq r) := by
  constructor
  · have ht := conditional_vertex_physical r hr0 hr1
    exact ⟨conditionalVertex r, ht.1.le, ht.2.le, conditional_cap_attained r hr0 hr1⟩
  · rintro v ⟨t, ht0, ht1, rfl⟩
    exact conditional_cap_global r t hr0 hr1

end FilteredF3
