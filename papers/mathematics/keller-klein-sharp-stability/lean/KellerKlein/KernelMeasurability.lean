import KellerKlein.KernelDefs
import KellerKlein.Vendor.PrawitzSignIntegrability

noncomputable section
open MeasureTheory

namespace KellerKlein

lemma measurable_rho : Measurable rho := by
  unfold rho
  fun_prop

lemma measurable_upperKernel (ξ : ℝ) : Measurable (upperKernel ξ) := by
  unfold upperKernel
  exact ((measurable_const.sub measurable_id).mul
    (Real.continuous_cos.measurable.comp ((measurable_const.mul measurable_const).mul measurable_id))).add
      (measurable_rho.mul (Real.continuous_sin.measurable.comp
        ((measurable_const.mul measurable_const).mul measurable_id)))

lemma intervalIntegrable_upperKernel (ξ : ℝ) :
    IntervalIntegrable (upperKernel ξ) volume 0 1 := by
  have h1 : Continuous (fun u : ℝ => (1 - u) * Real.cos (Real.pi * ξ * u)) := by fun_prop
  have h2 := Causalean.Stat.CLT.BerryEsseen.prawitz_sine_intervalIntegrable (Real.pi * ξ)
  have he : (fun u : ℝ => Causalean.Stat.CLT.BerryEsseen.prawitzSineWeight u *
      Real.sin (u * (Real.pi * ξ))) =
      (fun u : ℝ => rho u * Real.sin (Real.pi * ξ * u)) := by
    funext u
    unfold Causalean.Stat.CLT.BerryEsseen.prawitzSineWeight rho
    rw [mul_comm u (Real.pi * ξ)]
    ring
  rw [he] at h2
  exact (h1.intervalIntegrable 0 1).add h2

def cosineProfile (b t : ℝ) : ℝ := |Real.cos (b * t)| ^ (1 / b ^ 2 : ℝ)

lemma continuous_cosineProfile (b : ℝ) : Continuous (cosineProfile b) := by
  unfold cosineProfile
  apply (Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs.rpow_const
  intro t
  right
  positivity

lemma cosineProfile_nonneg (b t : ℝ) : 0 ≤ cosineProfile b t :=
  Real.rpow_nonneg (abs_nonneg _) _

lemma cosineProfile_le_one (b t : ℝ) : cosineProfile b t ≤ 1 := by
  apply Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) (by positivity)

lemma intervalIntegrable_upperKernel_cosineProfile (a b ξ : ℝ) :
    IntervalIntegrable (fun u => upperKernel ξ u * cosineProfile b (Real.pi * u / a))
      volume 0 1 := by
  apply (intervalIntegrable_upperKernel ξ).mul_continuousOn
  exact ((continuous_cosineProfile b).comp
    ((continuous_const.mul continuous_id).div_const a)).continuousOn

end KellerKlein
