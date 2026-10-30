import KellerKlein.GaussianTail
import KellerKlein.ZoneBKernel

noncomputable section

open Set MeasureTheory

namespace KellerKlein

set_option maxHeartbeats 800000

def cotangentRemainderIntegrand (a x s : ℝ) : ℝ :=
  ((1-a*s/Real.pi)*cotangentQ (a*s))*Real.sin (s*x)*gaussian s

def cotangentRemainderIntegral (a x : ℝ) : ℝ :=
  a/Real.pi * ∫ s in Ioo (0 : ℝ) (Real.pi/a), cotangentRemainderIntegrand a x s

def cotangentRemainderMajorant (a s : ℝ) : ℝ :=
  (a^3/30)*(s^3*gaussian s) +
    (Ioi (1/a)).indicator (fun t => (a/2)*(t*gaussian t)) s

lemma integrable_cotangentRemainderMajorant (a : ℝ) :
    Integrable (cotangentRemainderMajorant a) := by
  apply ((integrable_pow_gaussian 3).const_mul (a^3/30)).add
  have h : Integrable (fun t : ℝ => (a/2)*(t*gaussian t)) := by
    simpa only [pow_one] using (integrable_pow_gaussian 1).const_mul (a/2)
  exact h.indicator measurableSet_Ioi

lemma cotangentRemainderMajorant_nonneg {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    0 ≤ cotangentRemainderMajorant a s := by
  have hg := gaussian_nonneg s
  dsimp [cotangentRemainderMajorant]
  apply add_nonneg (by positivity)
  by_cases hm : s ∈ Ioi (1/a)
  · rw [indicator_of_mem hm]
    positivity
  · rw [indicator_of_not_mem hm]

lemma measurable_cotangentRemainderIntegrand (a x : ℝ) :
    Measurable (cotangentRemainderIntegrand a x) := by
  unfold cotangentRemainderIntegrand cotangentQ gaussian
  fun_prop

lemma abs_cotangentRemainderIntegrand_le {a x s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hsa : s < Real.pi/a) :
    |cotangentRemainderIntegrand a x s| ≤ cotangentRemainderMajorant a s := by
  have hu : 0 < a*s/Real.pi := div_pos (mul_pos ha hs) Real.pi_pos
  have hu1 : a*s/Real.pi < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    have h := (lt_div_iff₀ ha).mp hsa
    nlinarith
  have he : Real.pi*(a*s/Real.pi) = a*s := by field_simp
  have hg := gaussian_nonneg s
  have hsin : |cotangentRemainderIntegrand a x s| ≤
      |(1-a*s/Real.pi)*cotangentQ (a*s)| * gaussian s := by
    dsimp [cotangentRemainderIntegrand]
    rw [abs_mul, abs_mul, abs_of_pos (gaussian_pos s)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
      (gaussian_nonneg s)
  by_cases hsmall : s ≤ 1/a
  · have has : a*s ≤ 1 := by
      have h := (le_div_iff₀ ha).mp hsmall
      nlinarith
    have hq := abs_weighted_cotangentQ_small hu hu1 (by rwa [he])
    rw [he] at hq
    have hh := mul_le_mul_of_nonneg_right hq (gaussian_nonneg s)
    have hnot : s ∉ Ioi (1/a) := not_lt.mpr hsmall
    rw [cotangentRemainderMajorant, indicator_of_not_mem hnot, add_zero]
    calc
      |cotangentRemainderIntegrand a x s| ≤ (a*s)^3/30*gaussian s := hsin.trans hh
      _ = (a^3/30)*(s^3*gaussian s) := by ring
  · have hq := abs_weighted_cotangentQ_le hu hu1
    rw [he] at hq
    have hh := mul_le_mul_of_nonneg_right hq (gaussian_nonneg s)
    have hmem : s ∈ Ioi (1/a) := lt_of_not_ge hsmall
    rw [cotangentRemainderMajorant, indicator_of_mem hmem]
    have hn : 0 ≤ (a^3/30)*(s^3*gaussian s) := by positivity
    nlinarith only [hsin, hh, hn]

lemma integrableOn_cotangentRemainderIntegrand {a x : ℝ} (ha : 0 < a) :
    IntegrableOn (cotangentRemainderIntegrand a x) (Ioo (0 : ℝ) (Real.pi/a)) := by
  apply (integrable_cotangentRemainderMajorant a).integrableOn.mono'
    (measurable_cotangentRemainderIntegrand a x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simpa only [Real.norm_eq_abs] using abs_cotangentRemainderIntegrand_le ha hs.1 hs.2

lemma integral_cotangentRemainderMajorant {a : ℝ} (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), cotangentRemainderMajorant a s) =
      a^3/15+(a/2)*gaussian (1/a) := by
  have htail : Integrable (fun t : ℝ => (a/2)*(t*gaussian t)) := by
    simpa only [pow_one] using (integrable_pow_gaussian 1).const_mul (a/2)
  unfold cotangentRemainderMajorant
  rw [integral_add ((integrableOn_pow_gaussian 3).const_mul _)
    (htail.indicator measurableSet_Ioi).integrableOn,
    integral_const_mul, setIntegral_indicator measurableSet_Ioi]
  have hinter : Ioi (0 : ℝ) ∩ Ioi (1/a) = Ioi (1/a) := by
    rw [inter_eq_right]
    exact Ioi_subset_Ioi (by positivity : (0 : ℝ) ≤ 1/a)
  rw [hinter, integral_const_mul]
  have h3 : (∫ s in Ioi (0 : ℝ), s^3*gaussian s) = 2 := halfMoment_three
  have h1 : (∫ s in Ioi (1/a), s*gaussian s) = gaussian (1/a) := by
    simpa only [gaussianTailMoment, pow_one] using gaussianTailMoment_one (1/a)
  rw [h3, h1]
  ring

lemma abs_cotangentRemainderIntegral_le {a x : ℝ} (ha : 0 < a) :
    |cotangentRemainderIntegral a x| ≤
      a^4/(15*Real.pi)+(a^2/(2*Real.pi))*gaussian (1/a) := by
  have hi := integrableOn_cotangentRemainderIntegrand (x := x) ha
  have hm := (integrable_cotangentRemainderMajorant a).integrableOn
    (s := Ioo (0 : ℝ) (Real.pi/a))
  have h : |∫ s in Ioo (0 : ℝ) (Real.pi/a), cotangentRemainderIntegrand a x s| ≤
      a^3/15+(a/2)*gaussian (1/a) := by
    calc
      |∫ s in Ioo (0 : ℝ) (Real.pi/a), cotangentRemainderIntegrand a x s| ≤
          ∫ s in Ioo (0 : ℝ) (Real.pi/a), |cotangentRemainderIntegrand a x s| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ s in Ioo (0 : ℝ) (Real.pi/a), cotangentRemainderMajorant a s := by
        apply integral_mono_ae hi.abs hm
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact abs_cotangentRemainderIntegrand_le ha hs.1 hs.2
      _ ≤ ∫ s in Ioi (0 : ℝ), cotangentRemainderMajorant a s := by
        apply setIntegral_mono_set (integrable_cotangentRemainderMajorant a).integrableOn
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact cotangentRemainderMajorant_nonneg ha (show 0 < s from hs).le
        · exact Filter.Eventually.of_forall (fun s hs => hs.1)
      _ = a^3/15+(a/2)*gaussian (1/a) := integral_cotangentRemainderMajorant ha
  dsimp [cotangentRemainderIntegral]
  rw [abs_mul, abs_of_pos (div_pos ha Real.pi_pos)]
  have hh := mul_le_mul_of_nonneg_left h (div_nonneg ha.le Real.pi_pos.le)
  convert hh using 1 <;> ring

end KellerKlein
