import FiniteCycle
import ParameterBoundary

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace SevenCP

open FiniteCP

abbrev E := Space 4

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

def X (i : Fin 7) : E := ![
    !₂[768, 0, 7454, 0],
    !₂[481, 602, -1660, 7266],
    !₂[-170, 749, -6714, -3234],
    !₂[-695, 336, 4647, -5824],
    !₂[-695, -336, 4647, 5824],
    !₂[-170, -749, -6714, 3234],
    !₂[481, -602, -1660, -7266]] i

def Y (i : Fin 7) : E := ![
    !₂[259, -896, 9234, -7329],
    !₂[861, -350, 5097, 10633],
    !₂[812, 455, -11500, 2597],
    !₂[154, 917, 22, -11788],
    !₂[-623, 693, 11488, 2646],
    !₂[-931, -56, -5137, 10612],
    !₂[-532, -763, -9204, -7371]] i


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
