import KellerKlein.Vendor.PrawitzSignIntegrability
import KellerKlein.Vendor.TriangularCosineIntegral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import KellerKlein.Imports

/-! A recurrence proof of the pointwise Prawitz majorant.

The mathematical recurrence-and-limit argument was located in the public
CoolRmal/BerryEsseen project (commit bfb22608ad18b4fa9fda8dd9a1ed2c2b6fbc29e7).
The proof below is independently formalized for the pinned Lean 4.19 environment.
The endpoint integrability and triangular coefficient lemmas are adapted
from the Apache-2.0 CausalSmith sources, with originals retained separately.
-/

noncomputable section
open MeasureTheory Filter Topology
open Causalean.Stat.CLT.BerryEsseen

namespace KellerKlein

def prawitzA (x : ℝ) : ℝ := prawitzSignApprox (2 * Real.pi * x)

theorem prawitzA_integrand_integrable (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => prawitzSineWeight t * Real.sin (2 * Real.pi * x * t))
      volume 0 1 := by
  simpa only [mul_comm (2 * Real.pi * x)] using
    prawitz_sine_intervalIntegrable (2 * Real.pi * x)

theorem prawitzA_eq (x : ℝ) :
    prawitzA x = 2 * ∫ t in (0 : ℝ)..1,
      prawitzSineWeight t * Real.sin (2 * Real.pi * x * t) := by
  simp only [prawitzA, prawitzSignApprox, mul_comm (2 * Real.pi * x)]

@[simp] theorem prawitzA_zero : prawitzA 0 = 0 := by
  simp [prawitzA_eq]

theorem prawitzA_neg (x : ℝ) : prawitzA (-x) = -prawitzA x := by
  simp only [prawitzA_eq, mul_neg, neg_mul, Real.sin_neg, mul_neg,
    intervalIntegral.integral_neg]

theorem sine_frequency_integral {c : ℝ} (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..1, Real.sin (c * t)) = (1 - Real.cos c) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin hc]
  simp only [mul_zero, mul_one, integral_sin, Real.cos_zero, smul_eq_mul]
  ring

theorem prawitzA_shift_integrand (x t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    prawitzSineWeight t *
      (Real.sin (2 * Real.pi * (x + 1) * t) - Real.sin (2 * Real.pi * x * t)) =
      (1 - t) * (Real.cos (2 * Real.pi * (x + 1) * t) +
        Real.cos (2 * Real.pi * x * t)) +
      (Real.sin (2 * Real.pi * (x + 1) * t) -
        Real.sin (2 * Real.pi * x * t)) / Real.pi := by
  have hs : Real.sin (Real.pi * t) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht)
      (by nlinarith [Real.pi_pos])).ne'
  have harg : (2 * Real.pi * (x + 1) * t - 2 * Real.pi * x * t) / 2 =
      Real.pi * t := by ring
  rw [Real.sin_sub_sin, Real.cos_add_cos, harg]
  dsimp [prawitzSineWeight]
  field_simp
  <;> ring

theorem prawitzA_shift_integral (x : ℝ) :
    prawitzA (x + 1) - prawitzA x =
      Real.sinc (Real.pi * (x + 1)) ^ 2 + Real.sinc (Real.pi * x) ^ 2 +
      2 / Real.pi * ((∫ t in (0 : ℝ)..1, Real.sin (2 * Real.pi * (x + 1) * t)) -
        (∫ t in (0 : ℝ)..1, Real.sin (2 * Real.pi * x * t))) := by
  have hi (z : ℝ) : IntervalIntegrable
      (fun t : ℝ => (1-t) * Real.cos (2 * Real.pi * z * t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => (1-t) * Real.cos (2 * Real.pi * z * t))).intervalIntegrable 0 1
  have hj (z : ℝ) : IntervalIntegrable
      (fun t : ℝ => Real.sin (2 * Real.pi * z * t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => Real.sin (2 * Real.pi * z * t))).intervalIntegrable 0 1
  rw [prawitzA_eq (x+1), prawitzA_eq x, ← mul_sub,
    ← intervalIntegral.integral_sub (prawitzA_integrand_integrable (x+1))
      (prawitzA_integrand_integrable x)]
  have heq : (∫ t in (0 : ℝ)..1,
      (prawitzSineWeight t * Real.sin (2 * Real.pi * (x+1) * t) -
        prawitzSineWeight t * Real.sin (2 * Real.pi * x * t))) =
      ∫ t in (0 : ℝ)..1,
        ((1-t) * Real.cos (2 * Real.pi * (x+1) * t) +
        (1-t) * Real.cos (2 * Real.pi * x * t) +
        (Real.sin (2 * Real.pi * (x+1) * t) -
          Real.sin (2 * Real.pi * x * t)) / Real.pi) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] at ht
    have h := prawitzA_shift_integrand x t ht.1 ht.2
    convert h using 1 <;> ring
  rw [heq, intervalIntegral.integral_add ((hi (x+1)).add (hi x))
      (((hj (x+1)).sub (hj x)).div_const Real.pi),
    intervalIntegral.integral_add (hi (x+1)) (hi x),
    intervalIntegral.integral_div, intervalIntegral.integral_sub (hj (x+1)) (hj x),
    triangular_cosine_integral (x+1), triangular_cosine_integral x]
  ring

theorem prawitzA_one : prawitzA 1 = 1 := by
  have h := prawitzA_shift_integral 0
  have hs : (∫ t in (0 : ℝ)..1, Real.sin (2 * Real.pi * t)) = 0 := by
    rw [sine_frequency_integral (by positivity : 2 * Real.pi ≠ 0)]
    simp
  simpa [Real.sinc_of_ne_zero Real.pi_ne_zero, hs] using h

theorem prawitzA_shift {x : ℝ} (hx : 0 < x) :
    prawitzA (x + 1) - prawitzA x =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 / (x ^ 2 * (x + 1) ^ 2) := by
  have hx1 : 0 < x + 1 := by linarith
  have hn : 2 * Real.pi * x ≠ 0 := by positivity
  have hn1 : 2 * Real.pi * (x+1) ≠ 0 := by positivity
  rw [prawitzA_shift_integral, sine_frequency_integral hn1, sine_frequency_integral hn]
  rw [Real.sinc_of_ne_zero (by positivity : Real.pi * (x+1) ≠ 0),
    Real.sinc_of_ne_zero (by positivity : Real.pi * x ≠ 0)]
  rw [show Real.pi * (x+1) = Real.pi * x + Real.pi by ring, Real.sin_add_pi]
  rw [show 2 * Real.pi * (x+1) = 2 * (Real.pi * x) + 2 * Real.pi by ring,
    Real.cos_add_two_pi, show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
    Real.cos_two_mul_eq_one_sub]
  field_simp
  <;> ring

end KellerKlein
