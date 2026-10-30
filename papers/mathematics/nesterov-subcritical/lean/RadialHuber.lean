import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace NesterovModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialProj (x : E) : E := (max 1 ‖x‖)⁻¹ • x

noncomputable def radialHuber (x : E) : ℝ :=
  if ‖x‖ ≤ 1 then (‖x‖ ^ 2 + 1) / 2 else ‖x‖

theorem radialProj_of_norm_le {x : E} (hx : ‖x‖ ≤ 1) : radialProj x = x := by
  simp only [radialProj, max_eq_left hx, inv_one, one_smul]

theorem radialProj_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    radialProj x = ‖x‖⁻¹ • x := by
  rw [radialProj, max_eq_right hx]

theorem radialProj_norm_of_one_le {x : E} (hx : 1 ≤ ‖x‖) : ‖radialProj x‖ = 1 := by
  have hp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  rw [radialProj_of_one_le_norm hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]

theorem radialProj_norm_le_one (x : E) : ‖radialProj x‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · simpa only [radialProj_of_norm_le hx] using hx
  · rw [radialProj_norm_of_one_le (le_of_not_ge hx)]

theorem radialProj_recover (x : E) : max 1 ‖x‖ • radialProj x = x := by
  have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp only [radialProj, smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]

theorem radialProj_variational (x y : E) (hy : ‖y‖ ≤ 1) :
    inner (x - radialProj x) (y - radialProj x) ≤ (0 : ℝ) := by
  by_cases hx : ‖x‖ ≤ 1
  · simp only [radialProj_of_norm_le hx, sub_self, inner_zero_left, le_refl]
  · have hR : 1 ≤ ‖x‖ := le_of_not_ge hx
    have hpn := radialProj_norm_of_one_le hR
    have hr : ‖x‖ • radialProj x = x := by
      simpa only [max_eq_right hR] using radialProj_recover x
    have he : x - radialProj x = (‖x‖ - 1) • radialProj x := by
      rw [sub_smul, one_smul, hr]
    have hi := real_inner_le_norm (radialProj x) y
    rw [hpn, one_mul] at hi
    rw [he, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq, hpn]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hR) (by norm_num; linarith)

theorem radialProj_dist_le (x y : E) : ‖radialProj x - radialProj y‖ ≤ ‖x-y‖ := by
  have h1 := radialProj_variational x (radialProj y) (radialProj_norm_le_one y)
  have h2 := radialProj_variational y (radialProj x) (radialProj_norm_le_one x)
  have hid : inner (x-y) (radialProj x-radialProj y) - ‖radialProj x-radialProj y‖^2 =
      -(inner (x-radialProj x) (radialProj y-radialProj x) +
        inner (y-radialProj y) (radialProj x-radialProj y)) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (radialProj y) (radialProj x)]
    ring
  have hm : ‖radialProj x-radialProj y‖^2 ≤ inner (x-y) (radialProj x-radialProj y) := by
    linarith
  have hc := real_inner_le_norm (x-y) (radialProj x-radialProj y)
  by_cases hz : ‖radialProj x-radialProj y‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖radialProj x-radialProj y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_right hp).mp
    nlinarith

theorem radialProj_lipschitz : LipschitzWith 1 (radialProj : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using radialProj_dist_le x y

omit [InnerProductSpace ℝ E] in
theorem radialHuber_of_norm_le {x : E} (hx : ‖x‖ ≤ 1) :
    radialHuber x = (‖x‖^2+1)/2 := if_pos hx

omit [InnerProductSpace ℝ E] in
theorem radialHuber_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) : radialHuber x = ‖x‖ := by
  by_cases he : ‖x‖ ≤ 1
  · have hh : ‖x‖ = 1 := le_antisymm he hx
    simp only [radialHuber, hh]; norm_num
  · exact if_neg he

omit [InnerProductSpace ℝ E] in
theorem norm_le_radialHuber (x : E) : ‖x‖ ≤ radialHuber x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [radialHuber_of_norm_le hx]
    nlinarith [sq_nonneg (‖x‖-1)]
  · rw [radialHuber_of_one_le_norm (le_of_not_ge hx)]

theorem radialHuber_dual_bound (p y : E) (hp : ‖p‖ ≤ 1) :
    inner p y + (1-‖p‖^2)/2 ≤ radialHuber y := by
  have hc := real_inner_le_norm p y
  by_cases hy : ‖y‖ ≤ 1
  · rw [radialHuber_of_norm_le hy]
    nlinarith [sq_nonneg (‖p‖-‖y‖)]
  · rw [radialHuber_of_one_le_norm (le_of_not_ge hy)]
    have hh : 0 ≤ (1-‖p‖)*(2*‖y‖-‖p‖-1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem radialHuber_attained (x : E) :
    radialHuber x = inner (radialProj x) x + (1-‖radialProj x‖^2)/2 := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [radialHuber_of_norm_le hx, radialProj_of_norm_le hx,
      real_inner_self_eq_norm_sq]
    ring
  · have hR : 1 ≤ ‖x‖ := le_of_not_ge hx
    have hp : ‖x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
    rw [radialHuber_of_one_le_norm hR, radialProj_norm_of_one_le hR]
    norm_num only [one_pow, sub_self, zero_div, add_zero]
    rw [radialProj_of_one_le_norm hR, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring

theorem radialHuber_support (x y : E) :
    radialHuber x + inner (radialProj x) (y-x) ≤ radialHuber y := by
  have hh := radialHuber_dual_bound (radialProj x) y (radialProj_norm_le_one x)
  rw [radialHuber_attained x, inner_sub_right]
  linarith

theorem convexOn_univ_of_support {f : E → ℝ} (g : E → E)
    (hs : ∀ x y, f x + inner (g x) (y-x) ≤ f y) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hs z x) ha
  have hy := mul_le_mul_of_nonneg_left (hs z y) hb
  have he : a • (x-z) + b • (y-z) = 0 := by
    calc
      _ = (a • x+b • y) - (a+b) • z := by
        rw [add_smul, smul_sub, smul_sub]; abel
      _ = 0 := by rw [hab, one_smul]; exact sub_self _
  have hi : a * inner (g z) (x-z) + b * inner (g z) (y-z) = 0 := by
    rw [←inner_smul_right, ←inner_smul_right, ←inner_add_right, he, inner_zero_right]
  have hf : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  change f z ≤ a*f x+b*f y
  nlinarith

theorem radialHuber_convex : ConvexOn ℝ Set.univ (radialHuber : E → ℝ) :=
  convexOn_univ_of_support radialProj radialHuber_support

theorem radialHuber_remainder (x h : E) :
    ‖radialHuber (x+h)-radialHuber x-inner (radialProj x) h‖ ≤ ‖h‖^2 := by
  have hl := radialHuber_support x (x+h)
  have hu := radialHuber_support (x+h) x
  have he : x-(x+h) = -h := by abel
  simp only [add_sub_cancel_left] at hl
  rw [he, inner_neg_right] at hu
  have hp := radialProj_dist_le (x+h) x
  simp only [add_sub_cancel_left] at hp
  have hc := real_inner_le_norm (radialProj (x+h)-radialProj x) h
  have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg h)
  rw [inner_sub_left] at hc
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith

theorem radialHuber_hasFDerivAt (x : E) :
    HasFDerivAt radialHuber (innerSL ℝ (radialProj x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hb : (fun h : E => radialHuber (x+h)-radialHuber x-(innerSL ℝ (radialProj x)) h)
      =O[𝓝 0] (fun h : E => ‖h‖^2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with h
    change ‖radialHuber (x+h)-radialHuber x-inner (radialProj x) h‖ ≤ 1*‖‖h‖^2‖
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using
      radialHuber_remainder x h
  exact hb.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by decide : 1 < 2))

noncomputable def valley (e x : E) : ℝ := radialHuber x-inner e x
noncomputable def valleyGradient (e x : E) : E := radialProj x-e

theorem valley_support (e x y : E) :
    valley e x + inner (valleyGradient e x) (y-x) ≤ valley e y := by
  have hh := radialHuber_support x y
  simp only [valley, valleyGradient, inner_sub_left, inner_sub_right] at *
  linarith

theorem valley_convex (e : E) : ConvexOn ℝ Set.univ (valley e) :=
  convexOn_univ_of_support (valleyGradient e) (valley_support e)

theorem valley_hasFDerivAt (e x : E) :
    HasFDerivAt (valley e) (innerSL ℝ (valleyGradient e x)) x := by
  simpa only [valley, valleyGradient, map_sub] using
    (radialHuber_hasFDerivAt x).sub (innerSL ℝ e).hasFDerivAt

theorem valleyGradient_lipschitz (e : E) : LipschitzWith 1 (valleyGradient e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [valleyGradient, dist_eq_norm, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul]
    using radialProj_dist_le x y

theorem valleyGradient_norm_le_two {e : E} (he : ‖e‖=1) (x : E) :
    ‖valleyGradient e x‖ ≤ 2 := by
  have hh := norm_sub_le (radialProj x) e
  rw [he] at hh
  have hp := radialProj_norm_le_one x
  change ‖radialProj x-e‖ ≤ 2
  linarith

theorem valley_nonneg {e : E} (he : ‖e‖=1) (x : E) : 0 ≤ valley e x := by
  have hh := real_inner_le_norm e x
  rw [he,one_mul] at hh
  have hn := norm_le_radialHuber x
  unfold valley
  linarith

#print axioms radialHuber_hasFDerivAt
#print axioms valley_convex
#print axioms valleyGradient_lipschitz

end NesterovModel
