import KellerKlein.GaussianMoments
import KellerKlein.ZoneBKernel
import KellerKlein.ZoneBProfile
import KellerKlein.KernelRegularity

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace KellerKlein

set_option maxHeartbeats 800000

def primaryLossIntegrand (a ξ s : ℝ) : ℝ :=
  max 0 (-upperKernel ξ (a*s/Real.pi)) *
    (gaussian s - (Real.cos (a*s)) ^ (1/a^2 : ℝ))

def primaryLoss (a ξ : ℝ) : ℝ :=
  a/Real.pi * ∫ s in Ioo (0 : ℝ) (1/a), primaryLossIntegrand a ξ s

def smallLossMajorant (a ξ s : ℝ) : ℝ :=
  kernelLossCoeff ξ * a^2 * s^2 * gaussian s * gaussianProfileLoss a s

def largeLossMajorant (a s : ℝ) : ℝ :=
  (a^2*s^4/12+a^4*s^6/20+a*s^3/12+a^3*s^5/20)*gaussian s

lemma kernelLossCoeff_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ kernelLossCoeff ξ := by
  dsimp [kernelLossCoeff]
  positivity

lemma smallLossMajorant_eq (a ξ s : ℝ) :
    smallLossMajorant a ξ s = (kernelLossCoeff ξ*a^4/12)*(s^6*gaussian s) +
      (kernelLossCoeff ξ*a^6/20)*(s^8*gaussian s) := by
  dsimp [smallLossMajorant, gaussianProfileLoss]
  ring

lemma integrable_smallLossMajorant (a ξ : ℝ) : Integrable (smallLossMajorant a ξ) := by
  have he : smallLossMajorant a ξ = fun s =>
      (kernelLossCoeff ξ*a^4/12)*(s^6*gaussian s) +
        (kernelLossCoeff ξ*a^6/20)*(s^8*gaussian s) := funext (smallLossMajorant_eq a ξ)
  rw [he]
  exact ((integrable_pow_gaussian 6).const_mul (kernelLossCoeff ξ*a^4/12)).add
      ((integrable_pow_gaussian 8).const_mul (kernelLossCoeff ξ*a^6/20))

lemma integral_smallLossMajorant (a ξ : ℝ) :
    a/Real.pi * (∫ s in Ioi (0 : ℝ), smallLossMajorant a ξ s) =
      phi0*(5*a^5/4+21*a^7/4)*kernelLossCoeff ξ := by
  simp_rw [smallLossMajorant_eq]
  rw [integral_add
    ((integrableOn_pow_gaussian 6).const_mul _)
    ((integrableOn_pow_gaussian 8).const_mul _),
    integral_const_mul, integral_const_mul]
  change a/Real.pi*((kernelLossCoeff ξ*a^4/12)*halfMoment 6+
    (kernelLossCoeff ξ*a^6/20)*halfMoment 8) = _
  rw [halfMoment_six, halfMoment_eight]
  field_simp [Real.pi_ne_zero]
  ring

lemma primaryLossIntegrand_nonneg {a ξ s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hsa : s < 1/a) : 0 ≤ primaryLossIntegrand a ξ s := by
  have has : a*s < 1 := by
    have h := (lt_div_iff₀ ha).mp hsa
    nlinarith
  have hprofile := cosine_profile_le_gaussian ha hs.le
    (by linarith [Real.pi_gt_three] : a*s < Real.pi/2)
  exact mul_nonneg (le_max_left _ _) (sub_nonneg.mpr hprofile)

lemma primaryLossIntegrand_le_small {a ξ s : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ)
    (hs : 0 < s) (hsa : s < 1/a) :
    primaryLossIntegrand a ξ s ≤ smallLossMajorant a ξ s := by
  have has : a*s < 1 := by
    have h := (lt_div_iff₀ ha).mp hsa
    nlinarith
  have hu : 0 < a*s/Real.pi := div_pos (mul_pos ha hs) Real.pi_pos
  have hu1 : a*s/Real.pi < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hK := upperKernel_negativePart_le hξ hu hu1
  have he : Real.pi*(a*s/Real.pi) = a*s := by field_simp
  rw [he] at hK
  have hW := cosine_profile_loss_bound ha hs.le has.le
  have hW0 := sub_nonneg.mpr (cosine_profile_le_gaussian ha hs.le
    (by linarith [Real.pi_gt_three] : a*s < Real.pi/2))
  have hm := mul_le_mul hK hW hW0
    (mul_nonneg (kernelLossCoeff_nonneg hξ) (sq_nonneg _))
  convert hm using 1 <;> dsimp [primaryLossIntegrand, smallLossMajorant] <;> ring

lemma measurable_primaryLossIntegrand (a ξ : ℝ) : Measurable (primaryLossIntegrand a ξ) := by
  have hc : Continuous (fun s : ℝ => (Real.cos (a*s)) ^ (1/a^2 : ℝ)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).rpow_const
      (fun _ => Or.inr (by positivity))
  exact (measurable_const.max
    (((measurable_upperKernel ξ).comp
      ((measurable_const.mul measurable_id).div_const Real.pi)).neg)).mul
        (continuous_gaussian.measurable.sub hc.measurable)

lemma integrableOn_primaryLossIntegrand {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    IntegrableOn (primaryLossIntegrand a ξ) (Ioo (0 : ℝ) (1/a)) := by
  apply ((integrable_smallLossMajorant a ξ).integrableOn).mono'
    (measurable_primaryLossIntegrand a ξ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (primaryLossIntegrand_nonneg ha hs.1 hs.2)]
  exact primaryLossIntegrand_le_small ha hξ hs.1 hs.2

lemma primaryLoss_le_small {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    primaryLoss a ξ ≤ phi0*(5*a^5/4+21*a^7/4)*kernelLossCoeff ξ := by
  rw [← integral_smallLossMajorant a ξ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ha.le Real.pi_pos.le)
  calc
    (∫ s in Ioo (0 : ℝ) (1/a), primaryLossIntegrand a ξ s) ≤
        ∫ s in Ioo (0 : ℝ) (1/a), smallLossMajorant a ξ s := by
      apply integral_mono_ae (integrableOn_primaryLossIntegrand ha hξ)
        (integrable_smallLossMajorant a ξ).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact primaryLossIntegrand_le_small ha hξ hs.1 hs.2
    _ ≤ ∫ s in Ioi (0 : ℝ), smallLossMajorant a ξ s := by
      apply setIntegral_mono_set (integrable_smallLossMajorant a ξ).integrableOn
      · filter_upwards with s
        dsimp [smallLossMajorant, gaussianProfileLoss]
        have hk := kernelLossCoeff_nonneg hξ
        have hg := gaussian_nonneg s
        positivity
      · exact Filter.Eventually.of_forall (fun s hs => hs.1)

lemma largeLossMajorant_eq (a s : ℝ) :
    largeLossMajorant a s = (a^2/12)*(s^4*gaussian s) +
      (a^4/20)*(s^6*gaussian s) + (a/12)*(s^3*gaussian s) +
      (a^3/20)*(s^5*gaussian s) := by dsimp [largeLossMajorant]; ring

lemma integrable_largeLossMajorant (a : ℝ) : Integrable (largeLossMajorant a) := by
  have he : largeLossMajorant a = fun s => (a^2/12)*(s^4*gaussian s) +
      (a^4/20)*(s^6*gaussian s) + (a/12)*(s^3*gaussian s) +
      (a^3/20)*(s^5*gaussian s) := funext (largeLossMajorant_eq a)
  rw [he]
  exact ((((integrable_pow_gaussian 4).const_mul (a^2/12)).add
      ((integrable_pow_gaussian 6).const_mul (a^4/20))).add
      ((integrable_pow_gaussian 3).const_mul (a/12))).add
      ((integrable_pow_gaussian 5).const_mul (a^3/20))

lemma integral_largeLossMajorant (a : ℝ) :
    a/Real.pi * (∫ s in Ioi (0 : ℝ), largeLossMajorant a s) =
      phi0*a^3/4+a^2/(6*Real.pi)+3*phi0*a^5/4+2*a^4/(5*Real.pi) := by
  simp_rw [largeLossMajorant_eq]
  have h4 := (integrableOn_pow_gaussian 4).const_mul (a^2/12)
  have h6 := (integrableOn_pow_gaussian 6).const_mul (a^4/20)
  have h3 := (integrableOn_pow_gaussian 3).const_mul (a/12)
  have h5 := (integrableOn_pow_gaussian 5).const_mul (a^3/20)
  have h46 : IntegrableOn (fun s : ℝ => (a^2/12)*(s^4*gaussian s)+
      (a^4/20)*(s^6*gaussian s)) (Ioi 0) := h4.add h6
  have h463 : IntegrableOn (fun s : ℝ => (a^2/12)*(s^4*gaussian s)+
      (a^4/20)*(s^6*gaussian s)+(a/12)*(s^3*gaussian s)) (Ioi 0) := h46.add h3
  rw [integral_add h463 h5, integral_add h46 h3,
    integral_add h4 h6, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]
  change a/Real.pi*((a^2/12)*halfMoment 4+(a^4/20)*halfMoment 6+
    (a/12)*halfMoment 3+(a^3/20)*halfMoment 5) = _
  rw [halfMoment_four, halfMoment_six, halfMoment_three, halfMoment_five]
  field_simp [Real.pi_ne_zero]
  ring

lemma primaryLossIntegrand_le_large {a ξ s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hsa : s < 1/a) :
    primaryLossIntegrand a ξ s ≤ largeLossMajorant a s := by
  have has : a*s < 1 := by
    have h := (lt_div_iff₀ ha).mp hsa
    nlinarith
  have hu : 0 < a*s/Real.pi := div_pos (mul_pos ha hs) Real.pi_pos
  have hu1 : a*s/Real.pi < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hKabs := abs_upperKernel_le (ξ := ξ) hu hu1
  have he : Real.pi*(a*s/Real.pi) = a*s := by field_simp
  rw [he] at hKabs
  have hK : max 0 (-upperKernel ξ (a*s/Real.pi)) ≤ 1+1/(a*s) := by
    apply le_trans (max_le (abs_nonneg _) (neg_le_abs _)) hKabs
  have hW := cosine_profile_loss_bound ha hs.le has.le
  have hW0 := sub_nonneg.mpr (cosine_profile_le_gaussian ha hs.le
    (by linarith [Real.pi_gt_three] : a*s < Real.pi/2))
  have hm := mul_le_mul hK hW hW0 (by positivity : 0 ≤ 1+1/(a*s))
  have hp : (1+1/(a*s))*(gaussian s*gaussianProfileLoss a s) =
      largeLossMajorant a s := by
    dsimp [largeLossMajorant, gaussianProfileLoss]
    field_simp [ha.ne', hs.ne']
    ring
  exact hm.trans_eq hp

lemma primaryLoss_le_large {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    primaryLoss a ξ ≤
      phi0*a^3/4+a^2/(6*Real.pi)+3*phi0*a^5/4+2*a^4/(5*Real.pi) := by
  rw [← integral_largeLossMajorant a]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ha.le Real.pi_pos.le)
  calc
    (∫ s in Ioo (0 : ℝ) (1/a), primaryLossIntegrand a ξ s) ≤
        ∫ s in Ioo (0 : ℝ) (1/a), largeLossMajorant a s := by
      apply integral_mono_ae (integrableOn_primaryLossIntegrand ha hξ)
        (integrable_largeLossMajorant a).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact primaryLossIntegrand_le_large ha hs.1 hs.2
    _ ≤ ∫ s in Ioi (0 : ℝ), largeLossMajorant a s := by
      apply setIntegral_mono_set (integrable_largeLossMajorant a).integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        dsimp [largeLossMajorant]
        have hs0 : 0 < s := hs
        have hg := gaussian_nonneg s
        positivity
      · exact Filter.Eventually.of_forall (fun s hs => hs.1)

end KellerKlein
