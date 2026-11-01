import KellerKlein.GaussianError
import Mathlib.Probability.CDF

open Set MeasureTheory

namespace KellerKlein

lemma standardNormal_pdf_eq_phi : ProbabilityTheory.gaussianPDFReal 0 1 = phi := by
  funext x
  simp [ProbabilityTheory.gaussianPDFReal, phi, gaussian, phi0, mul_comm]

lemma integral_phi_total : (∫ x : ℝ, phi x) = 1 := by
  have h := ProbabilityTheory.integral_gaussianPDFReal_eq_one 0
    (by norm_num : (1 : NNReal) ≠ 0)
  rwa [standardNormal_pdf_eq_phi] at h

lemma standardNormal_cdf_eq_integral (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x = ∫ t in Iic x, phi t := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
    standardNormal_pdf_eq_phi, ENNReal.toReal_ofReal]
  exact integral_nonneg (fun t => (phi_pos t).le)

lemma integral_phi_Iic_zero : (∫ t in Iic (0 : ℝ), phi t) = 1 / 2 := by
  have h := intervalIntegral.integral_Iic_add_Ioi
    (integrable_phi.integrableOn (s := Iic (0 : ℝ)))
    (integrable_phi.integrableOn (s := Ioi (0 : ℝ)))
  rw [integral_phi_half, integral_phi_total] at h
  linarith

/-- The project's Gaussian target is exactly the CDF of Mathlib's N(0,1) law,
including negative arguments. -/
theorem standardNormal_cdf_eq (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x = 1 / 2 + c x := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (integrable_phi.integrableOn (s := Iic (0 : ℝ)))
    (integrable_phi.integrableOn (s := Iic x))
  rw [integral_phi_Iic_zero] at h
  change (∫ t in Iic x, phi t) - 1 / 2 = c x at h
  rw [standardNormal_cdf_eq_integral]
  linarith

end KellerKlein
