import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
Exact geometry of the equality circle b_z = |b|².  The first theorem is
polynomial and includes its boundary cases; the second uses actual square
roots to express the closest azimuth-preserving correction on a radius-r
sphere.  These are geometric lemmas, not a formalization of trace-norm
stability for arbitrary density operators.
-/

set_option autoImplicit false

namespace OrientationRigidity
noncomputable section

/-- Sharp squared-distance estimate for correction to the equality circle. -/
theorem circle_correction_polynomial (r z y w : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hy : 0 ≤ y) (hw : 0 ≤ w)
    (hz : z ^ 2 + y ^ 2 = r ^ 2)
    (hw2 : w ^ 2 = r ^ 2 * (1 - r ^ 2)) :
    (1 - r) * ((z - r ^ 2) ^ 2 + (y - w) ^ 2) ≤
      2 * (z - r ^ 2) ^ 2 := by
  have h1 : 0 < 1 - r := by linarith
  have hplus : 0 < 1 + r := by linarith
  have hzlo : -r ≤ z := by nlinarith [sq_nonneg y]
  have hzhi : z ≤ r := by nlinarith [sq_nonneg y]
  have hprod : 0 ≤ (r - z) * (r + z + 2 * r ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hsum : (z + r ^ 2) ^ 2 ≤ r ^ 2 * (1 + r) ^ 2 := by
    nlinarith
  have hnonneg : 0 ≤ 2 * y * w := by positivity
  have hden : r ^ 2 * (1 - r ^ 2) ≤ (y + w) ^ 2 := by
    nlinarith [sq_nonneg y]
  have hwpos : 0 < w := by
    have hs : 0 < r ^ 2 * (1 - r ^ 2) :=
      mul_pos (sq_pos_of_pos hr) (by nlinarith)
    nlinarith
  have hdpos : 0 < (y + w) ^ 2 := sq_pos_of_pos (by linarith)
  have hslope : (1 - r) * (z + r ^ 2) ^ 2 ≤
      (1 + r) * (y + w) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hsum (le_of_lt h1)
    have hb := mul_le_mul_of_nonneg_left hden (le_of_lt hplus)
    nlinarith
  have hfactor : (y - w) * (y + w) = -(z - r ^ 2) * (z + r ^ 2) := by
    nlinarith
  have hsquare : (y - w) ^ 2 * (y + w) ^ 2 =
      (z - r ^ 2) ^ 2 * (z + r ^ 2) ^ 2 := by
    calc
      _ = ((y - w) * (y + w)) ^ 2 := by ring
      _ = (-(z - r ^ 2) * (z + r ^ 2)) ^ 2 := by rw [hfactor]
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hslope (sq_nonneg (z - r ^ 2))
  have hmul : ((1 - r) * (y - w) ^ 2) * (y + w) ^ 2 ≤
      ((1 + r) * (z - r ^ 2) ^ 2) * (y + w) ^ 2 := by
    nlinarith [hsquare]
  have hratio := (mul_le_mul_right hdpos).mp hmul
  nlinarith

/-- Actual distance squared to the equality circle, at fixed azimuth. -/
def correctionCost (r z : ℝ) : ℝ :=
  (z - r ^ 2) ^ 2 +
    (Real.sqrt (r ^ 2 - z ^ 2) - r * Real.sqrt (1 - r ^ 2)) ^ 2

/-- Uniform estimate, including the zero-radius case. -/
theorem circle_correction_bound (r z : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : |z| ≤ r) :
    (1 - r) * correctionCost r z ≤ 2 * (z - r ^ 2) ^ 2 := by
  by_cases hr0 : r = 0
  · have hz0 : z = 0 := by simpa [hr0] using hz
    simp [correctionCost, hr0, hz0]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hzsq : z ^ 2 ≤ r ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg z) hr).mpr hz
      simpa only [sq_abs] using hh
    have hrad : 0 ≤ r ^ 2 - z ^ 2 := by linarith
    have hone : 0 ≤ 1 - r ^ 2 := by nlinarith
    have hy2 := Real.sq_sqrt hrad
    have hw2 := Real.sq_sqrt hone
    have hcir : z ^ 2 + Real.sqrt (r ^ 2 - z ^ 2) ^ 2 = r ^ 2 := by linarith
    have htarget : (r * Real.sqrt (1 - r ^ 2)) ^ 2 = r ^ 2 * (1 - r ^ 2) := by
      rw [mul_pow, hw2]
    exact circle_correction_polynomial r z _ _ hrp hr1 (Real.sqrt_nonneg _)
      (mul_nonneg hr (Real.sqrt_nonneg _)) hcir htarget

/-- The coefficient in the squared-distance estimate is sharp at the north pole. -/
theorem circle_correction_sharp (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r) * correctionCost r r = 2 * (r - r ^ 2) ^ 2 := by
  have hone : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt hone
  simp only [correctionCost, sub_self, Real.sqrt_zero, zero_sub, neg_sq, mul_pow]
  rw [hroot]
  ring

/-- Turning an orientation deficit into an actual correction-distance bound. -/
theorem correction_from_deficit (c r z e : ℝ)
    (hc : 0 < c) (hc1 : c < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : |z| ≤ r)
    (hgap : c * (1 - c) * (r ^ 2 - z) ^ 2 ≤ e) :
    c * (1 - c) * (1 - r) * correctionCost r z ≤ 2 * e := by
  have hcoef : 0 ≤ c * (1 - c) := mul_nonneg (le_of_lt hc) (by linarith)
  have hgeom := circle_correction_bound r z hr hr1 hz
  have hm := mul_le_mul_of_nonneg_left hgeom hcoef
  have hsq : (z - r ^ 2) ^ 2 = (r ^ 2 - z) ^ 2 := by ring
  rw [hsq] at hm
  nlinarith

end
end OrientationRigidity
