import KellerKlein.PrawitzLimit

noncomputable section
open MeasureTheory
open Causalean.Stat.CLT.BerryEsseen

namespace KellerKlein

theorem prawitzA_normalized (z : ℝ) :
    prawitzA (z/(2*Real.pi)) = prawitzSignApprox z := by
  unfold prawitzA
  congr 1
  field_simp

theorem prawitzS_div_sq_eq_sinc {x : ℝ} (hx : x ≠ 0) :
    prawitzS x/x^2 = Real.sinc (Real.pi*x)^2 := by
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
  simp only [prawitzS, div_pow, mul_pow, div_div]

theorem prawitzSignApprox_neg (z : ℝ) :
    prawitzSignApprox (-z) = -prawitzSignApprox z := by
  simp only [prawitzSignApprox, mul_neg, Real.sin_neg, mul_neg,
    intervalIntegral.integral_neg]

theorem prawitz_indicator_majorant (z : ℝ) :
    (if 0 ≤ z then (1 : ℝ) else 0) ≤
      (1+prawitzSignApprox z+Real.sinc (z/2)^2)/2 := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [if_neg (not_le.mpr hz)]
    have hr : 0 < (-z)/(2*Real.pi) := div_pos (neg_pos.mpr hz) (by positivity)
    have h := prawitzA_le_one hr
    rw [prawitzA_normalized, prawitzSignApprox_neg] at h
    nlinarith [sq_nonneg (Real.sinc (z/2))]
  · simp [prawitzSignApprox]
  · rw [if_pos hz.le]
    have hr : 0 < z/(2*Real.pi) := div_pos hz (by positivity)
    have h := one_le_prawitzA_plus_tail hr
    rw [prawitzA_normalized, prawitzS_div_sq_eq_sinc hr.ne'] at h
    have heq : Real.pi*(z/(2*Real.pi)) = z/2 := by field_simp; ring
    rw [heq] at h
    linarith

theorem prawitz_triangle_raw (z : ℝ) :
    Real.sinc (z/2)^2 = 2 * ∫ t in (0 : ℝ)..1,
      (1-t)*Real.cos (t*z) := by
  have h := triangular_cosine_integral (z/(2*Real.pi))
  have harg : Real.pi*(z/(2*Real.pi))=z/2 := by field_simp; ring
  rw [harg] at h
  have hfun : (fun t : ℝ => (1-t)*Real.cos (2*Real.pi*(z/(2*Real.pi))*t)) =
      (fun t : ℝ => (1-t)*Real.cos (t*z)) := by
    funext t
    congr 2
    field_simp
    ring
  rw [hfun] at h
  linarith

end KellerKlein
