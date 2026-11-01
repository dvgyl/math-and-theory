import KellerKlein.KernelBounds
import KellerKlein.KernelMeasurability

noncomputable section

open MeasureTheory

namespace KellerKlein

lemma abs_upperKernel_uniform {ξ u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    |upperKernel ξ u| ≤ 1+|ξ| := by
  have hr := rho_nonneg hu hu1
  have hru := rho_le_inv hu hu1
  have hy : 0 < Real.pi*u := mul_pos Real.pi_pos hu
  have hs : |Real.sin (Real.pi*ξ*u)| ≤ (Real.pi*u)*|ξ| := by
    have h := Real.abs_sin_le_abs (x := Real.pi*ξ*u)
    simpa only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hu, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hsin := mul_le_mul_of_nonneg_left hs hr
  have hdiv := mul_le_mul_of_nonneg_right hru
    (mul_nonneg hy.le (abs_nonneg ξ))
  have he : (1/(Real.pi*u))*((Real.pi*u)*|ξ|) = |ξ| := by
    field_simp [Real.pi_ne_zero, hu.ne']
  rw [he] at hdiv
  have hcos := mul_le_of_le_one_right (by linarith : 0 ≤ 1-u)
    (Real.abs_cos_le_one (Real.pi*ξ*u))
  calc
    |upperKernel ξ u| ≤ |(1-u)*Real.cos (Real.pi*ξ*u)|+
      |rho u*Real.sin (Real.pi*ξ*u)| := abs_add_le _ _
    _ = (1-u)*|Real.cos (Real.pi*ξ*u)|+rho u*|Real.sin (Real.pi*ξ*u)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-u), abs_of_nonneg hr]
    _ ≤ 1+|ξ| := by linarith

end KellerKlein
