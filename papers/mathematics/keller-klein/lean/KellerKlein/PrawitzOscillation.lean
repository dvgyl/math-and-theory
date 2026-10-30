import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import KellerKlein.Imports

noncomputable section
open MeasureTheory Filter Topology
open scoped FourierTransform

namespace KellerKlein

theorem tendsto_integral_mul_cos_atTop {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun w : ℝ => ∫ t : ℝ, f t * Real.cos (2 * Real.pi * t * w))
      atTop (𝓝 0) := by
  have hc : Integrable (fun t : ℝ => (f t : ℂ)) := hf.ofReal
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((Real.zero_at_infty_fourierIntegral (fun t : ℝ => (f t : ℂ))).mono_left
      atTop_le_cocompact)
  have heq (w : ℝ) : (Real.fourierIntegral (fun t : ℝ => (f t : ℂ)) w).re =
      ∫ t : ℝ, f t * Real.cos (2 * Real.pi * t * w) := by
    have hi₀ := (Real.fourierIntegral_convergent_iff w).mpr hc
    have hi : Integrable (fun t : ℝ => 𝐞 (-(t*w)) • (f t : ℂ)) := by
      simpa only [real_inner_comm] using hi₀
    rw [Real.fourierIntegral_real_eq] 
    change RCLike.re (∫ t : ℝ, 𝐞 (-(t*w)) • (f t : ℂ)) = _
    rw [← integral_re hi]
    apply integral_congr_ae
    filter_upwards [] with t
    change (𝐞 (-(t*w)) • (f t : ℂ)).re = _
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, zero_sub,
      mul_one, add_zero, Real.exp_zero, one_mul, mul_neg, Real.cos_neg]
    rw [mul_comm (f t)]
    congr 2
    ring
  simpa only [Function.comp_def, heq, Complex.zero_re] using h

theorem tendsto_intervalIntegral_mul_cos_atTop {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) :
    Tendsto (fun w : ℝ => ∫ t in (0 : ℝ)..1,
      f t * Real.cos (2 * Real.pi * t * w)) atTop (𝓝 0) := by
  let g : ℝ → ℝ := (Set.Ioc 0 1).indicator f
  have hg : Integrable g := hf.1.integrable_indicator measurableSet_Ioc
  have h := tendsto_integral_mul_cos_atTop hg
  have heq (w : ℝ) : (∫ t : ℝ, g t * Real.cos (2 * Real.pi * t * w)) =
      ∫ t in (0 : ℝ)..1, f t * Real.cos (2 * Real.pi * t * w) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1 <;> simp [g, ht]
  simpa only [heq] using h

end KellerKlein
