import KellerKlein.GaussianMoments

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace KellerKlein

set_option maxHeartbeats 800000

def gaussianD (x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), Real.sin (s*x) * gaussian s

def gaussianM (x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s * Real.cos (s*x) * gaussian s

def gaussianN (x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s^2 * Real.sin (s*x) * gaussian s

lemma integrable_pow_sin_gaussian (k : ℕ) (x : ℝ) :
    Integrable (fun s : ℝ => s^k * Real.sin (s*x) * gaussian s) := by
  have h := (integrable_pow_gaussian k).bdd_mul
    (f := fun s : ℝ => Real.sin (s*x))
    ((Real.continuous_sin.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    ⟨1, fun s => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (s*x)⟩
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

lemma integrable_pow_cos_gaussian (k : ℕ) (x : ℝ) :
    Integrable (fun s : ℝ => s^k * Real.cos (s*x) * gaussian s) := by
  have h := (integrable_pow_gaussian k).bdd_mul
    (f := fun s : ℝ => Real.cos (s*x))
    ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    ⟨1, fun s => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (s*x)⟩
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

lemma hasDerivAt_gaussian (s : ℝ) : HasDerivAt gaussian (-s * gaussian s) s := by
  convert (((hasDerivAt_pow 2 s).neg).div_const 2).exp using 1 <;>
    simp only [gaussian] <;> ring

lemma tendsto_pow_gaussian (k : ℕ) :
    Tendsto (fun s : ℝ => s^k * gaussian s) atTop (𝓝 0) := by
  have h := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
    (b := (1/2 : ℝ)) (by norm_num) (k : ℝ)
  have he : Tendsto (fun s : ℝ => Real.exp (-(1/2)*s)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by norm_num)
  have ht := h.trans_tendsto he
  convert ht using 1
  funext s
  simp only [Real.rpow_natCast, gaussian]
  congr 2
  ring

lemma tendsto_gaussian : Tendsto gaussian atTop (𝓝 0) := by
  simpa using tendsto_pow_gaussian 0

lemma tendsto_gaussian_cos (x : ℝ) :
    Tendsto (fun s : ℝ => gaussian s * Real.cos (s*x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun s => ?_) tendsto_gaussian
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos s)]
  exact mul_le_of_le_one_right (gaussian_nonneg s) (Real.abs_cos_le_one _)

lemma tendsto_mul_gaussian_sin (x : ℝ) :
    Tendsto (fun s : ℝ => s * gaussian s * Real.sin (s*x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_pow_gaussian 1)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  simp only [pow_one]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs,
    abs_of_pos (gaussian_pos s)]
  exact mul_le_of_le_one_right (mul_nonneg hs (gaussian_nonneg s)) (Real.abs_sin_le_one _)

lemma abs_gaussianD_le : ∀ x : ℝ, |gaussianD x| ≤ Real.pi * phi0 := by
  intro x
  have hi := (integrable_pow_sin_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_zero, one_mul] at hi
  calc
    |gaussianD x| ≤ ∫ s in Ioi (0 : ℝ), |Real.sin (s*x) * gaussian s| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi (0 : ℝ), gaussian s := by
      apply integral_mono_ae hi.abs integrable_gaussian.integrableOn
      filter_upwards with s
      rw [abs_mul, abs_of_pos (gaussian_pos s)]
      exact mul_le_of_le_one_left (gaussian_nonneg s) (Real.abs_sin_le_one _)
    _ = Real.pi * phi0 := by simpa [halfMoment] using halfMoment_zero

lemma abs_gaussianM_le (x : ℝ) : |gaussianM x| ≤ 1 := by
  have hi := (integrable_pow_cos_gaussian 1 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_one] at hi
  calc
    |gaussianM x| ≤ ∫ s in Ioi (0 : ℝ), |s * Real.cos (s*x) * gaussian s| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi (0 : ℝ), s * gaussian s := by
      apply integral_mono_ae hi.abs (by simpa using integrableOn_pow_gaussian 1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (gaussian_pos s)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hs.le (Real.abs_cos_le_one _)) (gaussian_nonneg s)
    _ = 1 := by simpa [halfMoment] using halfMoment_one

lemma abs_gaussianN_le (x : ℝ) : |gaussianN x| ≤ Real.pi * phi0 := by
  have hi := (integrable_pow_sin_gaussian 2 x).integrableOn (s := Ioi (0 : ℝ))
  calc
    |gaussianN x| ≤ ∫ s in Ioi (0 : ℝ), |s^2 * Real.sin (s*x) * gaussian s| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi (0 : ℝ), s^2 * gaussian s := by
      apply integral_mono_ae hi.abs (integrableOn_pow_gaussian 2)
      filter_upwards with s
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos (gaussian_pos s)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (sq_nonneg s) (Real.abs_sin_le_one _)) (gaussian_nonneg s)
    _ = Real.pi * phi0 := halfMoment_two

lemma gaussianD_le_self {x : ℝ} (hx : 0 ≤ x) : gaussianD x ≤ x := by
  have hi := (integrable_pow_sin_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_zero, one_mul] at hi
  calc
    gaussianD x ≤ ∫ s in Ioi (0 : ℝ), x * (s * gaussian s) := by
      apply integral_mono_ae hi (by simpa using (integrableOn_pow_gaussian 1).const_mul x)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h := mul_le_mul_of_nonneg_right (Real.sin_le (mul_nonneg hs.le hx))
        (gaussian_nonneg s)
      simpa only [mul_comm, mul_left_comm, mul_assoc] using h
    _ = x := by
      rw [integral_const_mul]
      have h : (∫ s in Ioi (0 : ℝ), s * gaussian s) = 1 := by
        simpa [halfMoment] using halfMoment_one
      rw [h, mul_one]

lemma gaussianM_eq (x : ℝ) : gaussianM x = 1 - x * gaussianD x := by
  let f : ℝ → ℝ := fun s => gaussian s * Real.cos (s*x)
  let f' : ℝ → ℝ := fun s => -(s * Real.cos (s*x) * gaussian s) -
    x * (Real.sin (s*x) * gaussian s)
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    convert (hasDerivAt_gaussian s).mul (((hasDerivAt_id s).mul_const x).cos) using 1 <;>
      dsimp [f, f'] <;> ring
  have hc := (integrable_pow_cos_gaussian 1 x).integrableOn (s := Ioi (0 : ℝ))
  have hs := (integrable_pow_sin_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_one] at hc
  simp only [pow_zero, one_mul] at hs
  have hi : IntegrableOn f' (Ioi 0) := hc.neg.sub (hs.const_mul x)
  have hn : IntegrableOn (fun s => -(s * Real.cos (s*x) * gaussian s)) (Ioi 0) := hc.neg
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (tendsto_gaussian_cos x)
  change (∫ s in Ioi (0 : ℝ), -(s * Real.cos (s*x) * gaussian s) -
    x * (Real.sin (s*x) * gaussian s)) = 0 - f 0 at he
  rw [integral_sub hn (hs.const_mul x), integral_neg, integral_const_mul] at he
  simp only [f, gaussian_zero, zero_mul, Real.cos_zero, mul_one, sub_self, zero_sub] at he
  change -gaussianM x - x * gaussianD x = -1 at he
  linarith

lemma gaussianN_eq (x : ℝ) : gaussianN x = gaussianD x + x * gaussianM x := by
  let f : ℝ → ℝ := fun s => s * gaussian s * Real.sin (s*x)
  let f' : ℝ → ℝ := fun s => Real.sin (s*x) * gaussian s -
    s^2 * Real.sin (s*x) * gaussian s + x * (s * Real.cos (s*x) * gaussian s)
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    convert ((hasDerivAt_id s).mul (hasDerivAt_gaussian s)).mul
      (((hasDerivAt_id s).mul_const x).sin) using 1 <;> dsimp [f, f'] <;> ring
  have h0 := (integrable_pow_sin_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
  have h1 := (integrable_pow_cos_gaussian 1 x).integrableOn (s := Ioi (0 : ℝ))
  have h2 := (integrable_pow_sin_gaussian 2 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hi : IntegrableOn f' (Ioi 0) := (h0.sub h2).add (h1.const_mul x)
  have h02 : IntegrableOn (fun s => Real.sin (s*x) * gaussian s -
      s^2 * Real.sin (s*x) * gaussian s) (Ioi 0) := h0.sub h2
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (tendsto_mul_gaussian_sin x)
  change (∫ s in Ioi (0 : ℝ), Real.sin (s*x) * gaussian s -
    s^2 * Real.sin (s*x) * gaussian s + x * (s * Real.cos (s*x) * gaussian s)) = 0 - f 0 at he
  rw [integral_add h02 (h1.const_mul x), integral_sub h0 h2,
    integral_const_mul] at he
  simp only [f, zero_mul, sub_zero] at he
  change gaussianD x - gaussianN x + x * gaussianM x = 0 at he
  linarith

lemma mul_gaussianD_le_two (x : ℝ) : x * gaussianD x ≤ 2 := by
  have h := (abs_le.mp (abs_gaussianM_le x)).1
  rw [gaussianM_eq] at h
  linarith

lemma gaussianN_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    gaussianN x ≤ 2*x := by
  have hD := gaussianD_le_self hx
  have hsq : 0 ≤ 1-x^2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hD hsq
  rw [gaussianN_eq, gaussianM_eq]
  nlinarith [mul_nonneg hx (sq_nonneg x)]

lemma integral_cos_phi (x : ℝ) :
    (∫ s : ℝ, Real.cos (s*x) * phi s) = gaussian x := by
  have hpdf : ProbabilityTheory.gaussianPDFReal 0 1 = phi := by
    funext s
    simp [ProbabilityTheory.gaussianPDFReal, phi, gaussian, phi0, mul_comm]
  let f : ℝ → ℂ := fun s => (phi s : ℂ) * Complex.exp ((x : ℂ) * s * Complex.I)
  have hi : Integrable f := by
    have h := integrable_phi.ofReal.bdd_mul
      (f := fun s : ℝ => Complex.exp ((x : ℂ) * s * Complex.I))
      (by apply Continuous.aestronglyMeasurable; fun_prop)
      ⟨1, fun s => by simp [Complex.norm_exp]⟩
    simpa only [f, mul_comm] using h
  have hc := ProbabilityTheory.charFun_gaussianReal (μ := 0) (v := 1) x
  rw [charFun_apply_real,
    ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0),
    hpdf] at hc
  simp only [Complex.real_smul] at hc
  have he : (∫ s : ℝ, f s) = Complex.exp (-(x : ℂ)^2 / 2) := by
    simpa only [f, Complex.ofReal_zero, mul_zero, NNReal.coe_one, Complex.ofReal_one,
      one_mul, zero_mul, zero_sub, neg_div] using hc
  have hr := congrArg Complex.re he
  have hri : (∫ s : ℝ, (f s).re) = (∫ s : ℝ, f s).re := integral_re hi
  rw [← hri] at hr
  simpa [f, pow_two, Complex.mul_re, Complex.mul_im, Complex.exp_re, gaussian, mul_comm] using hr

lemma integral_cos_gaussian_half (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), Real.cos (s*x) * gaussian s) = Real.pi * phi x := by
  let f : ℝ → ℝ := fun s => Real.cos (s*x) * gaussian s
  have heven : ∀ s : ℝ, f |s| = f s := by
    intro s
    rcases le_or_lt 0 s with hs | hs
    · rw [abs_of_nonneg hs]
    · simp only [abs_of_neg hs, f, neg_mul, Real.cos_neg, gaussian_neg]
  have hh : (∫ s : ℝ, f s) = 2 * ∫ s in Ioi (0 : ℝ), f s := by
    simpa only [heven] using (integral_comp_abs (f := f))
  have hf : (∫ s : ℝ, f s) * phi0 = gaussian x := by
    simpa only [phi, ← mul_assoc, integral_mul_const, f] using integral_cos_phi x
  rw [hh] at hf
  have hn := congrArg (fun t : ℝ => t * gaussian x) two_pi_phi0_sq
  dsimp only at hn
  apply mul_left_cancel₀ (ne_of_gt phi0_pos)
  unfold phi
  change phi0 * (∫ s in Ioi (0 : ℝ), f s) = phi0 * (Real.pi * (gaussian x * phi0))
  nlinarith

lemma integral_mul_sin_gaussian_half (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), s * Real.sin (s*x) * gaussian s) = Real.pi * x * phi x := by
  let f : ℝ → ℝ := fun s => gaussian s * Real.sin (s*x)
  let f' : ℝ → ℝ := fun s => -(s * Real.sin (s*x) * gaussian s) +
    x * (Real.cos (s*x) * gaussian s)
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt f (f' s) s := by
    intro s hs
    convert (hasDerivAt_gaussian s).mul (((hasDerivAt_id s).mul_const x).sin) using 1 <;>
      dsimp [f, f'] <;> ring
  have h1 := (integrable_pow_sin_gaussian 1 x).integrableOn (s := Ioi (0 : ℝ))
  have h0 := (integrable_pow_cos_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
  simp only [pow_one] at h1
  simp only [pow_zero, one_mul] at h0
  have hn : IntegrableOn (fun s => -(s * Real.sin (s*x) * gaussian s)) (Ioi 0) := h1.neg
  have hi : IntegrableOn f' (Ioi 0) := hn.add (h0.const_mul x)
  have ht : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun s => ?_) tendsto_gaussian
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos s)]
    exact mul_le_of_le_one_right (gaussian_nonneg s) (Real.abs_sin_le_one _)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  change (∫ s in Ioi (0 : ℝ), -(s * Real.sin (s*x) * gaussian s) +
    x * (Real.cos (s*x) * gaussian s)) = 0 - f 0 at he
  rw [integral_add hn (h0.const_mul x), integral_neg, integral_const_mul,
    integral_cos_gaussian_half] at he
  simp only [f, zero_mul, Real.sin_zero, mul_zero, sub_zero] at he
  nlinarith

def gaussianSineIntegral (x : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (Real.sin (s*x) / s) * gaussian s

lemma abs_sin_mul_div_le (s x : ℝ) : |Real.sin (s*x) / s| ≤ |x| := by
  by_cases hs : s = 0
  · simp [hs]
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hs)).2
  simpa only [abs_mul, mul_comm] using (Real.abs_sin_le_abs (x := s*x))

lemma integrable_sin_div_gaussian (x : ℝ) :
    Integrable (fun s : ℝ => (Real.sin (s*x) / s) * gaussian s) := by
  have hm : Measurable (fun s : ℝ => (Real.sin (s*x) / s) * gaussian s) :=
    ((Real.measurable_sin.comp (measurable_id.mul measurable_const)).div measurable_id).mul
      continuous_gaussian.measurable
  apply Integrable.mono' (integrable_gaussian.const_mul |x|) hm.aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos s)]
  exact mul_le_mul_of_nonneg_right (abs_sin_mul_div_le s x) (gaussian_nonneg s)

lemma hasDerivAt_gaussianSineIntegral (x : ℝ) :
    HasDerivAt gaussianSineIntegral (Real.pi * phi x) x := by
  let F : ℝ → ℝ → ℝ := fun y s => (Real.sin (s*y) / s) * gaussian s
  let F' : ℝ → ℝ → ℝ := fun y s => Real.cos (s*y) * gaussian s
  have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (Ioi 0)) :=
    Filter.Eventually.of_forall fun y => (integrable_sin_div_gaussian y).integrableOn.aestronglyMeasurable
  have hi : Integrable (F x) (volume.restrict (Ioi 0)) :=
    (integrable_sin_div_gaussian x).integrableOn
  have hm' : AEStronglyMeasurable (F' x) (volume.restrict (Ioi 0)) := by
    have h := (integrable_pow_cos_gaussian 0 x).integrableOn (s := Ioi (0 : ℝ))
    simpa only [F', pow_zero, one_mul] using h.aestronglyMeasurable
  have hb : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ y ∈ Metric.ball x 1, ‖F' y s‖ ≤ gaussian s := by
    filter_upwards with s
    intro y hy
    dsimp only [F']
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos s)]
    exact mul_le_of_le_one_left (gaussian_nonneg s) (Real.abs_cos_le_one _)
  have hd : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ y ∈ Metric.ball x 1, HasDerivAt (fun z => F z s) (F' y s) y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro y hy
    have hs0 : 0 < s := hs
    convert (((hasDerivAt_id y).const_mul s).sin.div_const s).mul_const
      (gaussian s) using 1 <;> dsimp [F, F'] <;> field_simp [hs0.ne'] <;> ring
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (by norm_num : (0 : ℝ) < 1) hm hi hm' hb integrable_gaussian.integrableOn hd).2
  change HasDerivAt gaussianSineIntegral
    (∫ s in Ioi (0 : ℝ), Real.cos (s*x) * gaussian s) x at hh
  rwa [integral_cos_gaussian_half] at hh

lemma integral_sin_div_gaussian_half (x : ℝ) :
    gaussianSineIntegral x = Real.pi * c x := by
  have hi : IntervalIntegrable (fun y => Real.pi * phi y) volume (0 : ℝ) x :=
    (continuous_const.mul continuous_phi).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hasDerivAt_gaussianSineIntegral y) hi
  simp only [gaussianSineIntegral, mul_zero, Real.sin_zero, zero_div, zero_mul,
    integral_zero, sub_zero] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h.symm

end KellerKlein
