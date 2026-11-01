import KellerKlein.KernelBounds

noncomputable section

namespace KellerKlein.ZoneA

def A (ξ : ℝ) : ℝ := ξ ^ 2 / 2 + ξ / 3 + ξ ^ 3 / 6
def AL (ξ : ℝ) : ℝ := ξ ^ 2 / 2 + ξ / 2 + ξ ^ 3 / 6
def B (ξ : ℝ) : ℝ := (ξ ^ 2 / 2 + ξ / 3) / Real.pi
def C (ξ : ℝ) : ℝ := ξ ^ 4 / 24 + ξ ^ 3 / 18 + ξ ^ 5 / 120
def D (ξ : ℝ) : ℝ := ξ ^ 5 / (360 * Real.pi)

def lowerPoly (ξ y : ℝ) : ℝ := 1 + ξ - y / Real.pi - AL ξ * y ^ 2

def upperPoly (ξ y : ℝ) : ℝ :=
  1 + ξ - y / Real.pi - A ξ * y ^ 2 + B ξ * y ^ 3 + C ξ * y ^ 4 + D ξ * y ^ 7

lemma upperKernel_eq_y (ξ u : ℝ) :
    upperKernel ξ u = (1 - (Real.pi * u) / Real.pi) * Real.cos (ξ * (Real.pi * u)) +
      rho u * Real.sin (ξ * (Real.pi * u)) := by
  have h1 : Real.pi * u / Real.pi = u := by field_simp
  have h2 : ξ * (Real.pi * u) = Real.pi * ξ * u := by ring
  rw [h1, h2]
  rfl

lemma upperKernel_le_upperPoly {ξ u : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hu : 0 < u) (hu1 : u < 1) : upperKernel ξ u ≤ upperPoly ξ (Real.pi * u) := by
  let y := Real.pi * u
  have hy : 0 < y := mul_pos Real.pi_pos hu
  have heyu : y / Real.pi = u := by dsimp [y]; field_simp
  have hc : 0 ≤ 1 - y / Real.pi := by rw [heyu]; linarith
  have hz : 0 ≤ ξ * y := mul_nonneg hξ hy.le
  have hzp : ξ * y ≤ Real.pi := by
    dsimp [y]
    have hm : ξ * u ≤ 1 / 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz hzp
  have hrho : rho u ≤ (1 / y + y ^ 2 / (3 * Real.pi)) - y / 3 := by
    convert rho_upper_quadratic hu hu1 using 1 <;> dsimp [y] <;> ring
  have hcos := mul_le_mul_of_nonneg_left (cos_upper_quartic hz) hc
  have hsup := mul_le_mul_of_nonneg_left (sin_upper_quintic hz)
    (show 0 ≤ 1 / y + y ^ 2 / (3 * Real.pi) by positivity)
  have hslo := mul_le_mul_of_nonneg_left (sin_lower_cubic hz)
    (show 0 ≤ y / 3 by positivity)
  have hr := mul_le_mul_of_nonneg_right hrho hs
  have hbound : upperKernel ξ u ≤
      (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2 + (ξ * y) ^ 4 / 24) +
      (1 / y + y ^ 2 / (3 * Real.pi)) *
        (ξ * y - (ξ * y) ^ 3 / 6 + (ξ * y) ^ 5 / 120) -
      (y / 3) * (ξ * y - (ξ * y) ^ 3 / 6) := by
    rw [upperKernel_eq_y]
    change (1 - y / Real.pi) * Real.cos (ξ * y) + rho u * Real.sin (ξ * y) ≤ _
    nlinarith only [hcos, hsup, hslo, hr]
  have he :
      (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2 + (ξ * y) ^ 4 / 24) +
      (1 / y + y ^ 2 / (3 * Real.pi)) *
        (ξ * y - (ξ * y) ^ 3 / 6 + (ξ * y) ^ 5 / 120) -
      (y / 3) * (ξ * y - (ξ * y) ^ 3 / 6) =
      upperPoly ξ y - (ξ ^ 4 / (24 * Real.pi) + ξ ^ 3 / (18 * Real.pi)) * y ^ 5 := by
    unfold upperPoly A B C D
    field_simp [hy.ne', Real.pi_ne_zero]
    ring
  rw [he] at hbound
  have hn : 0 ≤ (ξ ^ 4 / (24 * Real.pi) + ξ ^ 3 / (18 * Real.pi)) * y ^ 5 := by
    positivity
  change upperKernel ξ u ≤ upperPoly ξ y
  linarith

lemma lowerPoly_le_upperKernel {ξ u : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hu : 0 < u) (hu1 : u < 1) : lowerPoly ξ (Real.pi * u) ≤ upperKernel ξ u := by
  let y := Real.pi * u
  have hy : 0 < y := mul_pos Real.pi_pos hu
  have heyu : y / Real.pi = u := by dsimp [y]; field_simp
  have hc : 0 ≤ 1 - y / Real.pi := by rw [heyu]; linarith
  have hz : 0 ≤ ξ * y := mul_nonneg hξ hy.le
  have hzp : ξ * y ≤ Real.pi := by
    dsimp [y]
    have hm : ξ * u ≤ 1 / 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz hzp
  have hcos := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := ξ * y)) hc
  have hr := mul_le_mul_of_nonneg_right (rho_lower_linear hu hu1) hs
  change (1 / y - y / 2) * Real.sin (ξ * y) ≤ rho u * Real.sin (ξ * y) at hr
  by_cases hcoef : 0 ≤ 1 / y - y / 2
  · have hsin := mul_le_mul_of_nonneg_left (sin_lower_cubic hz) hcoef
    have hb : (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2) +
        (1 / y - y / 2) * (ξ * y - (ξ * y) ^ 3 / 6) ≤ upperKernel ξ u := by
      rw [upperKernel_eq_y]
      change _ ≤ (1 - y / Real.pi) * Real.cos (ξ * y) + rho u * Real.sin (ξ * y)
      nlinarith only [hcos, hsin, hr]
    have he : (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2) +
        (1 / y - y / 2) * (ξ * y - (ξ * y) ^ 3 / 6) =
        lowerPoly ξ y + ξ ^ 2 * y ^ 3 / (2 * Real.pi) + ξ ^ 3 * y ^ 4 / 12 := by
      unfold lowerPoly AL
      field_simp [hy.ne', Real.pi_ne_zero]
      ring
    rw [he] at hb
    have hn1 : 0 ≤ ξ ^ 2 * y ^ 3 / (2 * Real.pi) := by positivity
    have hn2 : 0 ≤ ξ ^ 3 * y ^ 4 / 12 := by positivity
    change lowerPoly ξ y ≤ upperKernel ξ u
    linarith
  · have hsin := mul_le_mul_of_nonpos_left (Real.sin_le hz) (le_of_not_ge hcoef)
    have hb : (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2) +
        (1 / y - y / 2) * (ξ * y) ≤ upperKernel ξ u := by
      rw [upperKernel_eq_y]
      change _ ≤ (1 - y / Real.pi) * Real.cos (ξ * y) + rho u * Real.sin (ξ * y)
      nlinarith only [hcos, hsin, hr]
    have he : (1 - y / Real.pi) * (1 - (ξ * y) ^ 2 / 2) +
        (1 / y - y / 2) * (ξ * y) =
        lowerPoly ξ y + ξ ^ 2 * y ^ 3 / (2 * Real.pi) + ξ ^ 3 * y ^ 2 / 6 := by
      unfold lowerPoly AL
      field_simp [hy.ne', Real.pi_ne_zero]
      ring
    rw [he] at hb
    have hn1 : 0 ≤ ξ ^ 2 * y ^ 3 / (2 * Real.pi) := by positivity
    have hn2 : 0 ≤ ξ ^ 3 * y ^ 2 / 6 := by positivity
    change lowerPoly ξ y ≤ upperKernel ξ u
    linarith

end KellerKlein.ZoneA
