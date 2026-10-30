import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# A scalar trigonometric support inequality

This module proves the exceptional residue bound needed by the analytic
Fourier-cycle construction.  The proof reduces it to a polynomial inequality,
without a numerical approximation or a differentiation argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace TrigSupport

def cubicSquare (s r : ℝ) : ℝ :=
  (1 + s) * (1 + r) * (1 - s / 2 + (s - 1 / 2) * r) ^ 2

theorem cubicSquare_le_one {s r : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1 / 8)
    (hrmin : 4 * s ≤ r) (hrmax : r ≤ 1) : cubicSquare s r ≤ 1 := by
  have hr : 0 ≤ r := by linarith
  have hs4 : 4 * s ≤ 1 := by linarith
  have hq : 0 ≤ 1 - 2 * s := by linarith
  have hqmax : 1 - 2 * s ≤ 1 := by linarith
  have hqmin : 3 / 4 ≤ 1 - 2 * s := by linarith
  let Q := r ^ 2 + 4 * s * r + 16 * s ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQmax : Q ≤ 2 * (r + 4 * s) := by
    dsimp [Q]
    have h₁ := mul_nonneg hr (sub_nonneg.mpr hrmax)
    have h₂ := mul_nonneg hr (sub_nonneg.mpr hs4)
    have h₃ := mul_nonneg (by positivity : 0 ≤ 4 * s) (sub_nonneg.mpr hs4)
    nlinarith
  have hqQ : (1 - 2 * s) ^ 2 * Q ≤ 2 * (1 - 2 * s) * (r + 4 * s) := by
    have h₁ := mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hqmax)) hQ
    have h₂ := mul_nonneg hq (sub_nonneg.mpr hQmax)
    nlinarith
  have hqr : 6 * s ≤ (1 - 2 * s) * (r + 4 * s) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hqmin) (by positivity : 0 ≤ r + 4 * s)
    nlinarith
  have hD : 0 ≤ 3 * (1 - 2 * s) * (r + 4 * s) -
      (1 - 2 * s) ^ 2 * Q - 3 * s * (2 - s) := by
    nlinarith [sq_nonneg s]
  have hmono : cubicSquare s r ≤ cubicSquare s (4 * s) := by
    have h := mul_nonneg
      (mul_nonneg (by positivity : 0 ≤ (1 + s) / 4) (sub_nonneg.mpr hrmin)) hD
    have he : cubicSquare s (4 * s) - cubicSquare s r =
        (1 + s) / 4 * (r - 4 * s) *
          (3 * (1 - 2 * s) * (r + 4 * s) -
            (1 - 2 * s) ^ 2 * Q - 3 * s * (2 - s)) := by
      dsimp [cubicSquare, Q]
      ring
    linarith
  have hs2 : s ^ 2 ≤ 1 / 64 := by
    have h := mul_nonneg hs (sub_nonneg.mpr hsmax)
    nlinarith
  have hend : cubicSquare s (4 * s) ≤ 1 := by
    have h₁ := mul_nonneg (sq_nonneg s) (by linarith : 0 ≤ 27 / 4 - 125 / 4 * s)
    have h₂ := mul_nonneg (pow_nonneg hs 4) (by linarith : 0 ≤ 27 - 64 * s ^ 2)
    unfold cubicSquare
    nlinarith
  exact hmono.trans hend

theorem cubic_pair_le_one {s r x y : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1 / 8)
    (hrmin : 4 * s ≤ r) (hrmax : r ≤ 1)
    (hsquares : x ^ 2 + y ^ 2 = 1 + s * r)
    (hproduct : 2 * x * y = r + s) :
    x ^ 3 + y ^ 3 ≤ 1 := by
  have hsum : (x + y) ^ 2 = (1 + s) * (1 + r) := by nlinarith
  have hdiff : x ^ 2 - x * y + y ^ 2 = 1 - s / 2 + (s - 1 / 2) * r := by
    nlinarith
  have hsq : (x ^ 3 + y ^ 3) ^ 2 = cubicSquare s r := by
    calc
      (x ^ 3 + y ^ 3) ^ 2 = (x + y) ^ 2 * (x ^ 2 - x * y + y ^ 2) ^ 2 := by ring
      _ = cubicSquare s r := by rw [hsum, hdiff]; rfl
  have hbound := cubicSquare_le_one hs hsmax hrmin hrmax
  have hunit : (x ^ 3 + y ^ 3) ^ 2 ≤ 1 := by rw [hsq]; exact hbound
  nlinarith [sq_nonneg (x ^ 3 + y ^ 3 - 1)]

theorem cos_sq_add_sin_shift_sq (a t : ℝ) :
    Real.cos a ^ 2 + Real.sin (a + t) ^ 2 =
      1 + Real.sin t * Real.sin (2 * a + t) := by
  have h := Real.two_mul_sin_mul_sin (2 * a + t) t
  rw [show 2 * a + t - t = 2 * a by ring,
    show 2 * a + t + t = 2 * (a + t) by ring] at h
  rw [Real.cos_sq, Real.sin_sq_eq_half_sub]
  nlinarith

theorem two_cos_mul_sin_shift (a t : ℝ) :
    2 * Real.cos a * Real.sin (a + t) =
      Real.sin (2 * a + t) + Real.sin t := by
  have h := Real.two_mul_sin_mul_cos (a + t) a
  rw [show a + t - a = t by ring, show a + t + a = 2 * a + t by ring] at h
  nlinarith

/-- The nontrivial trigonometric residue estimate in the analytic construction.
All range hypotheses are explicit; no grid or asymptotic premise is assumed. -/
theorem cos_cube_add_sin_cube_le_one {t a : ℝ}
    (ht : 0 < t) (htsmall : Real.sin t ≤ 1 / 8)
    (ha : 0 ≤ a) (hat : a + t ≤ Real.pi / 2)
    (hr : 4 * Real.sin t ≤ Real.sin (2 * a + t)) :
    Real.cos a ^ 3 + Real.sin (a + t) ^ 3 ≤ 1 := by
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [Real.pi_pos])
  exact cubic_pair_le_one hs htsmall hr (Real.sin_le_one _)
    (cos_sq_add_sin_shift_sq a t) (two_cos_mul_sin_shift a t)

end TrigSupport

#print axioms TrigSupport.cos_cube_add_sin_cube_le_one
