import KellerKlein.CotangentRemainder

noncomputable section

namespace KellerKlein

set_option maxHeartbeats 800000

def kernelLossCoeff (ξ : ℝ) : ℝ := ξ^2/2 + ξ^3/6 + ξ/2

lemma upperKernel_lower_global {ξ u : ℝ} (hξ : 0 ≤ ξ)
    (hu : 0 < u) (hu1 : u < 1) :
    1 + ξ - u - kernelLossCoeff ξ * (Real.pi*u)^2 ≤ upperKernel ξ u := by
  let y := Real.pi*u
  let h := rho u - 1/y
  have hy : 0 < y := mul_pos Real.pi_pos hu
  have hz : 0 ≤ ξ*y := mul_nonneg hξ hy.le
  have h0 : h ≤ 0 := by
    dsimp [h, y]
    linarith [rho_le_inv hu hu1]
  have hl : -y/2 ≤ h := by
    dsimp [h, y]
    linarith [rho_lower_linear hu hu1]
  have hhs : -(y*(ξ*y)/2) ≤ h*Real.sin (ξ*y) := by
    have h1 := mul_le_mul_of_nonpos_left (Real.sin_le hz) h0
    have h2 := mul_le_mul_of_nonneg_right hl hz
    calc
      -(y*(ξ*y)/2) = (-y/2)*(ξ*y) := by ring
      _ ≤ h*(ξ*y) := h2
      _ ≤ h*Real.sin (ξ*y) := h1
  have hc := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := ξ*y)) (by linarith : 0 ≤ 1-u)
  have hs := mul_le_mul_of_nonneg_left (sin_lower_cubic hz)
    (by positivity : 0 ≤ 1/y)
  have he : upperKernel ξ u = (1-u)*Real.cos (ξ*y) +
      (1/y)*Real.sin (ξ*y) + h*Real.sin (ξ*y) := by
    dsimp [upperKernel, h, y]
    rw [show Real.pi*ξ*u = ξ*(Real.pi*u) by ring]
    ring
  have hb : (1-u)*(1-(ξ*y)^2/2) + (1/y)*(ξ*y-(ξ*y)^3/6) -
      y*(ξ*y)/2 ≤ upperKernel ξ u := by
    rw [he]
    linarith
  have hp : (1-u)*(1-(ξ*y)^2/2) + (1/y)*(ξ*y-(ξ*y)^3/6) -
      y*(ξ*y)/2 = 1+ξ-u-kernelLossCoeff ξ*y^2+u*ξ^2*y^2/2 := by
    dsimp [kernelLossCoeff]
    field_simp [hy.ne']
    ring
  rw [hp] at hb
  have hn : 0 ≤ u*ξ^2*y^2/2 := by positivity
  change 1+ξ-u-kernelLossCoeff ξ*y^2 ≤ upperKernel ξ u
  linarith

lemma upperKernel_negativePart_le {ξ u : ℝ} (hξ : 0 ≤ ξ)
    (hu : 0 < u) (hu1 : u < 1) :
    max 0 (-upperKernel ξ u) ≤ kernelLossCoeff ξ * (Real.pi*u)^2 := by
  apply max_le
  · dsimp [kernelLossCoeff]
    positivity
  · have h := upperKernel_lower_global hξ hu hu1
    linarith

lemma abs_upperKernel_le {ξ u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    |upperKernel ξ u| ≤ 1 + 1/(Real.pi*u) := by
  have hr := rho_nonneg hu hu1
  have hru := rho_le_inv hu hu1
  have h1 := Real.abs_cos_le_one (Real.pi*ξ*u)
  have h2 := Real.abs_sin_le_one (Real.pi*ξ*u)
  calc
    |upperKernel ξ u| ≤ |(1-u)*Real.cos (Real.pi*ξ*u)| +
        |rho u*Real.sin (Real.pi*ξ*u)| := abs_add_le _ _
    _ = (1-u)*|Real.cos (Real.pi*ξ*u)|+rho u*|Real.sin (Real.pi*ξ*u)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-u), abs_of_nonneg hr]
    _ ≤ (1-u)+rho u := by
      have hc := mul_le_of_le_one_right (by linarith : 0 ≤ 1-u) h1
      have hs := mul_le_of_le_one_right hr h2
      linarith
    _ ≤ 1+1/(Real.pi*u) := by linarith

def cotangentQ (y : ℝ) : ℝ := Real.cos y / Real.sin y - 1/y + y/3

lemma rho_remainder_eq (u : ℝ) (hu : u ≠ 0) :
    (1-u)*cotangentQ (Real.pi*u) =
      rho u - 1/(Real.pi*u) + (1-u)*(Real.pi*u)/3 := by
  dsimp [cotangentQ, rho]
  field_simp [Real.pi_ne_zero, hu]
  ring

lemma weighted_cotangentQ_nonpos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (1-u)*cotangentQ (Real.pi*u) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
  exact cotangent_remainder_nonpos (mul_pos Real.pi_pos hu)
    (by nlinarith [Real.pi_pos])

lemma abs_weighted_cotangentQ_le {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    |(1-u)*cotangentQ (Real.pi*u)| ≤ Real.pi*u/2 := by
  rw [abs_of_nonpos (weighted_cotangentQ_nonpos hu hu1), rho_remainder_eq u hu.ne']
  have h := rho_lower_linear hu hu1
  have h1u : 0 ≤ 1-u := by linarith
  have hn : 0 ≤ (1-u)*(Real.pi*u)/3 := by positivity
  linarith

lemma abs_weighted_cotangentQ_small {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hy : Real.pi*u ≤ 1) :
    |(1-u)*cotangentQ (Real.pi*u)| ≤ (Real.pi*u)^3/30 := by
  have hq := cotangent_remainder_lower (mul_pos Real.pi_pos hu)
    (le_trans hy (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi/2))
  have h := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ 1-u)
  rw [abs_of_nonpos (weighted_cotangentQ_nonpos hu hu1)]
  have hy0 : 0 ≤ (Real.pi*u)^3 := by positivity
  have huq : 0 ≤ u*(Real.pi*u)^3 := by positivity
  change (1-u)*(-((Real.pi*u)^3/32)) ≤ (1-u)*cotangentQ (Real.pi*u) at h
  nlinarith

end KellerKlein
