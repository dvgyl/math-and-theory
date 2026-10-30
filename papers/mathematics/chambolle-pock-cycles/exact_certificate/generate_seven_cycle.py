#!/usr/bin/env python3
"""Convert the exact rational witness to integer-coordinate Lean source.

No optimizer output is trusted. The generated file proves every supporting
inequality over an entire parameter rectangle using the Lean kernel.
"""
from fractions import Fraction
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
data = json.loads((root / 'exact_certificate/period7_rational_certificate.json').read_text())
scale = 14000
def matrix(name):
    rows = [[Fraction(v)*scale for v in row] for row in data[name]]
    assert all(v.denominator == 1 for row in rows for v in row)
    return '![\n    ' + ',\n    '.join('!₂[' + ', '.join(str(v.numerator) for v in row) + ']' for row in rows) + ']'

prefix = '''import FiniteCycle
import ParameterBoundary

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace SevenCP

open FiniteCP

abbrev E := Space 4

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

'''
body = '''

theorem X_sum_zero : (∑ i : Fin 7, X i) = 0 := by
  ext j
  fin_cases j <;> norm_num [X, Fin.sum_univ_succ, Matrix.cons_val_succ]

theorem Y_sum_zero : (∑ i : Fin 7, Y i) = 0 := by
  ext j
  fin_cases j <;> norm_num [Y, Fin.sum_univ_succ, Matrix.cons_val_succ]

theorem X_zero_ne_one : X 0 ≠ X 1 := by
  intro h
  have he := congrArg (fun z : E => z 0) h
  norm_num [X] at he

/-- Exact supporting inequalities on an open-width rectangle of step parameters.
All coordinates are integers; no floating-point certificate enters this theorem. -/
theorem normal_certificate {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) : NormalCertificate X Y κ θ := by
  have hκ : 0 ≤ κ := by linarith
  have hprodlo : 0 ≤ κ * θ := mul_nonneg hκ hθlo
  have hprodhi : κ * θ ≤ κ / 400 := by
    have h := mul_nonneg hκ (sub_nonneg.mpr hθhi)
    nlinarith
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Y, nextIndex, Matrix.cons_val_succ, PiLp.inner_apply,
        Fin.sum_univ_succ, real_inner_eq_re_inner, RCLike.inner_apply]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Y, nextIndex, Matrix.cons_val_succ, PiLp.inner_apply,
        Fin.sum_univ_succ, real_inner_eq_re_inner, RCLike.inner_apply] <;>
      nlinarith

theorem strict_normal_certificate {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) :
    (∀ i j, j ≠ nextIndex i →
      ⟪X i - Y i - X (nextIndex i), X j - X (nextIndex i)⟫ < 0) ∧
    (∀ i j, j ≠ nextIndex i →
      ⟪Y i + κ • ((1 + θ) • X (nextIndex i) - θ • X i) - Y (nextIndex i),
        Y j - Y (nextIndex i)⟫ < 0) := by
  have hκ : 0 ≤ κ := by linarith
  have hprodlo : 0 ≤ κ * θ := mul_nonneg hκ hθlo
  have hprodhi : κ * θ ≤ κ / 400 := by
    have h := mul_nonneg hκ (sub_nonneg.mpr hθhi)
    nlinarith
  constructor
  · intro i j hne
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Y, nextIndex, Matrix.cons_val_succ, PiLp.inner_apply,
        Fin.sum_univ_succ, real_inner_eq_re_inner, RCLike.inner_apply] at hne ⊢
  · intro i j hne
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Y, nextIndex, Matrix.cons_val_succ, PiLp.inner_apply,
        Fin.sum_univ_succ, real_inner_eq_re_inner, RCLike.inner_apply] at hne ⊢ <;>
      nlinarith

theorem compact_saddle :
    IsCompact (hull X) ∧ IsCompact (hull Y) ∧
    Convex ℝ (hull X) ∧ Convex ℝ (hull Y) ∧
    IsSaddle (hull X) (hull Y) 0 0 :=
  ⟨hull_compact X, hull_compact Y, hull_convex X, hull_convex Y,
    origin_saddle X Y X_sum_zero Y_sum_zero⟩

theorem actual_seven_cycle {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) :
    (∀ k : ℕ, (cpMap X Y κ θ)^[k] (X 0, Y 0) = orbit X Y k) ∧
    (∀ k : ℕ, orbit X Y (k + 7) = orbit X Y k) ∧
    ¬ ∃ w, Filter.Tendsto (fun k : ℕ => (cpMap X Y κ θ)^[k] (X 0, Y 0))
      Filter.atTop (nhds w) := by
  have h := normal_certificate hκlo hκhi hθlo hθhi
  exact ⟨iterate_eq_orbit X Y κ θ h, orbit_periodic X Y,
    certified_nonconvergence X Y κ θ h 0 1 X_zero_ne_one⟩

theorem below_three_cycle_and_quadratic {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) :
    κ < CPSharpness.threeCycleBoundary θ ∧ κ < 4 / (1 + 2 * θ) := by
  have hpoly : (29 / 10 : ℝ) ^ 2 * (1 + θ) ^ 2 -
      2 * (29 / 10 : ℝ) * (1 + 3 * θ) - 3 < 0 := by
    have h := mul_nonneg hθlo (sub_nonneg.mpr hθhi)
    nlinarith
  have hb : (29 / 10 : ℝ) < CPSharpness.threeCycleBoundary θ := by
    by_contra hh
    have h := (CPSharpness.polynomial_iff_boundary (by norm_num : (0 : ℝ) ≤ 29 / 10) hθlo).mpr
      (le_of_not_gt hh)
    linarith
  constructor
  · linarith
  · rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + 2 * θ)]
    have hκ : 0 ≤ κ := by linarith
    have h := mul_nonneg hκ (sub_nonneg.mpr hθhi)
    nlinarith

end SevenCP
'''
source = prefix + 'def X (i : Fin 7) : E := ' + matrix('X') + ' i\n\n' + 'def Y (i : Fin 7) : E := ' + matrix('Y') + ' i\n' + body
(root / 'lean' / 'SevenCycle.lean').write_text(source)
print('SevenCycle.lean generated from exact rational coordinates; scale =', scale)
