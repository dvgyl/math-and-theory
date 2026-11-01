import QPermanentResearch.JensenGap
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
An exact bound for the closed-form spherical logarithmic potential.

The inputs a,b,h are squared coordinate moduli; s is the modulus of the
complex quadratic form.  This file proves the complete scalar geometric
inequality.  The identification of the logarithmic integral with this
closed form is a separate analytic statement and is not assumed to have
been formalized here.
-/

namespace QPermanentResearch

theorem potential_log_le_vertical {Q s : ℝ}
    (hQ : 0 < Q) (hs : 0 ≤ s) (hsQ : s ≤ Q) :
    Real.log ((Q + Real.sqrt (Q^2-s^2))/2) ≤ Q-1 := by
  have hrad : 0 ≤ Q^2-s^2 := by nlinarith
  have hr := Real.sqrt_nonneg (Q^2-s^2)
  have hrsq := Real.sq_sqrt hrad
  have hrQ : Real.sqrt (Q^2-s^2) ≤ Q := by nlinarith
  have hpos : 0 < (Q + Real.sqrt (Q^2-s^2))/2 := by positivity
  have hh := Real.log_le_sub_one_of_pos hpos
  linarith

theorem potential_log_le_quadratic {Q s : ℝ}
    (hQ : 0 < Q) (hQone : Q ≤ 1) (hs : 0 ≤ s) (hsQ : s ≤ Q) :
    Real.log ((Q + Real.sqrt (Q^2-s^2))/2) ≤ -s^2/4 := by
  have hrad : 0 ≤ Q^2-s^2 := by nlinarith
  have hr := Real.sqrt_nonneg (Q^2-s^2)
  have hrsq := Real.sq_sqrt hrad
  have hrQ : Real.sqrt (Q^2-s^2) ≤ Q := by nlinarith
  have hdiff : 0 ≤ Q - Real.sqrt (Q^2-s^2) := sub_nonneg.mpr hrQ
  have hsum : Q + Real.sqrt (Q^2-s^2) ≤ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hdiff
  have hpos : 0 < (Q + Real.sqrt (Q^2-s^2))/2 := by positivity
  have hh := Real.log_le_sub_one_of_pos hpos
  nlinarith

theorem outside_caps_quadratic_modulus {a b h τ ρ s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hsum : a+b+h=1) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (haCap : a ≤ 1-ρ^2) (hbCap : b ≤ 1-ρ^2)
    (hhsmall : h < ρ^2/2) (hτsq : τ^2 ≤ 1)
    (hs : 2*Real.sqrt (a*b)-τ^2*h ≤ s) : ρ/2 ≤ s := by
  have hrhosq : ρ^2 ≤ 1/4 := by nlinarith
  have hproduct := mul_nonneg (sub_nonneg.mpr haCap) (sub_nonneg.mpr hbCap)
  have hab : (1-ρ^2)*(ρ^2-h) ≤ a*b := by nlinarith
  have hleft : (3/4 : ℝ) ≤ 1-ρ^2 := by linarith
  have hright : ρ^2/2 ≤ ρ^2-h := by linarith
  have hmul := mul_le_mul hleft hright (by positivity : (0:ℝ) ≤ ρ^2/2)
    (by linarith : (0:ℝ) ≤ 1-ρ^2)
  have hablower : ρ^2/4 ≤ a*b := by nlinarith
  have habnonneg : 0 ≤ a*b := mul_nonneg ha hb
  have hroot := Real.sqrt_nonneg (a*b)
  have hrootsq := Real.sq_sqrt habnonneg
  have hrootlower : ρ ≤ 2*Real.sqrt (a*b) := by nlinarith
  have htauh := mul_le_mul_of_nonneg_right hτsq hh
  nlinarith

/-- Quantitative two-pole gap for the explicit logarithm/radical formula. -/
theorem closed_potential_outside_caps {a b h τ ρ Q s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hsum : a+b+h=1) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (haCap : a ≤ 1-ρ^2) (hbCap : b ≤ 1-ρ^2)
    (hτsq : τ^2 ≤ 1) (hQeq : Q=a+b+τ^2*h) (hQ : 0 < Q)
    (hsnonneg : 0 ≤ s) (hsQ : s ≤ Q)
    (hsLower : 2*Real.sqrt (a*b)-τ^2*h ≤ s) :
    Real.log ((Q + Real.sqrt (Q^2-s^2))/2) ≤
      -(min ((1-τ^2)/2) (1/16))*ρ^2 := by
  have htauh := mul_le_mul_of_nonneg_right hτsq hh
  have hQone : Q ≤ 1 := by linarith
  by_cases hhsmall : h < ρ^2/2
  · have hsLower' := outside_caps_quadratic_modulus ha hb hh hsum hρ hρhalf
      haCap hbCap hhsmall hτsq hsLower
    have hlog := potential_log_le_quadratic hQ hQone hsnonneg hsQ
    have hmin := min_le_right ((1-τ^2)/2) (1/16 : ℝ)
    have hm := mul_le_mul_of_nonneg_right hmin (sq_nonneg ρ)
    nlinarith
  · have hbig : ρ^2/2 ≤ h := le_of_not_gt hhsmall
    have hm := mul_le_mul_of_nonneg_left hbig (sub_nonneg.mpr hτsq)
    have hlog := potential_log_le_vertical hQ hsnonneg hsQ
    have hmin := min_le_left ((1-τ^2)/2) (1/16 : ℝ)
    have hminmul := mul_le_mul_of_nonneg_right hmin (sq_nonneg ρ)
    nlinarith

#print axioms potential_log_le_vertical
#print axioms potential_log_le_quadratic
#print axioms outside_caps_quadratic_modulus
#print axioms closed_potential_outside_caps

end QPermanentResearch
