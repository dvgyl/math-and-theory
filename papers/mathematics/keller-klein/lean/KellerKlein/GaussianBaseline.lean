import KellerKlein.GaussianTail
import KellerKlein.ZoneBRemainder

noncomputable section

open Set MeasureTheory

namespace KellerKlein

set_option maxHeartbeats 800000

def gaussianBaselineIntegrand (a x s : ℝ) : ℝ :=
  Real.cos (s*x)*gaussian s - (a/Real.pi)*(s*Real.cos (s*x)*gaussian s) +
    (1/a)*((Real.sin (s*x)/s)*gaussian s) -
    (a/3)*(s*Real.sin (s*x)*gaussian s) +
    (a^2/(3*Real.pi))*(s^2*Real.sin (s*x)*gaussian s)

def gaussianBaselineValue (a x : ℝ) : ℝ :=
  c x + a*phi x-a^2*gaussianM x/Real.pi^2-a^2*x*phi x/3+
    a^3*gaussianN x/(3*Real.pi^2)

lemma integrable_gaussianBaselineIntegrand (a x : ℝ) :
    Integrable (gaussianBaselineIntegrand a x) := by
  have hc0 : Integrable (fun s : ℝ => Real.cos (s*x)*gaussian s) := by
    simpa only [pow_zero, one_mul] using integrable_pow_cos_gaussian 0 x
  have hc1 : Integrable (fun s : ℝ => s*Real.cos (s*x)*gaussian s) := by
    simpa only [pow_one] using integrable_pow_cos_gaussian 1 x
  have hs1 : Integrable (fun s : ℝ => s*Real.sin (s*x)*gaussian s) := by
    simpa only [pow_one] using integrable_pow_sin_gaussian 1 x
  exact (((hc0.sub (hc1.const_mul (a/Real.pi))).add
    ((integrable_sin_div_gaussian x).const_mul (1/a))).sub
    (hs1.const_mul (a/3))).add
    ((integrable_pow_sin_gaussian 2 x).const_mul (a^2/(3*Real.pi)))

lemma integral_gaussianBaselineIntegrand {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    a/Real.pi * (∫ s in Ioi (0 : ℝ), gaussianBaselineIntegrand a x s) =
      gaussianBaselineValue a x := by
  have hc0 : IntegrableOn (fun s : ℝ => Real.cos (s*x)*gaussian s) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using (integrable_pow_cos_gaussian 0 x).integrableOn
  have hc1 : IntegrableOn (fun s : ℝ => s*Real.cos (s*x)*gaussian s) (Ioi 0) := by
    simpa only [pow_one] using (integrable_pow_cos_gaussian 1 x).integrableOn
  have hs1 : IntegrableOn (fun s : ℝ => s*Real.sin (s*x)*gaussian s) (Ioi 0) := by
    simpa only [pow_one] using (integrable_pow_sin_gaussian 1 x).integrableOn
  have hsm := (integrable_sin_div_gaussian x).integrableOn (s := Ioi (0 : ℝ))
  have hs2 := (integrable_pow_sin_gaussian 2 x).integrableOn (s := Ioi (0 : ℝ))
  have hc01 : IntegrableOn (fun s : ℝ => Real.cos (s*x)*gaussian s-
      (a/Real.pi)*(s*Real.cos (s*x)*gaussian s)) (Ioi 0) := hc0.sub (hc1.const_mul _)
  have hc01m : IntegrableOn (fun s : ℝ => Real.cos (s*x)*gaussian s-
      (a/Real.pi)*(s*Real.cos (s*x)*gaussian s)+(1/a)*((Real.sin (s*x)/s)*gaussian s))
      (Ioi 0) := hc01.add (hsm.const_mul _)
  have hc01m1 : IntegrableOn (fun s : ℝ => Real.cos (s*x)*gaussian s-
      (a/Real.pi)*(s*Real.cos (s*x)*gaussian s)+(1/a)*((Real.sin (s*x)/s)*gaussian s)-
      (a/3)*(s*Real.sin (s*x)*gaussian s)) (Ioi 0) := hc01m.sub (hs1.const_mul _)
  unfold gaussianBaselineIntegrand
  rw [integral_add hc01m1 (hs2.const_mul (a^2/(3*Real.pi))),
    integral_sub hc01m (hs1.const_mul (a/3)),
    integral_add hc01 (hsm.const_mul (1/a)),
    integral_sub hc0 (hc1.const_mul (a/Real.pi)),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cos_gaussian_half, integral_mul_sin_gaussian_half]
  change a/Real.pi*(Real.pi*phi x-(a/Real.pi)*gaussianM x+
    (1/a)*gaussianSineIntegral x-(a/3)*(Real.pi*x*phi x)+
    (a^2/(3*Real.pi))*gaussianN x) = _
  rw [integral_sin_div_gaussian_half]
  dsimp [gaussianBaselineValue]
  field_simp [ha, Real.pi_ne_zero]
  ring

lemma gaussian_kernel_decomposition {a x s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hsa : s < Real.pi/a) :
    upperKernel (x/a) (a*s/Real.pi)*gaussian s =
      gaussianBaselineIntegrand a x s+cotangentRemainderIntegrand a x s := by
  have hy : 0 < a*s := mul_pos ha hs
  have hyp : a*s < Real.pi := by
    have h := (lt_div_iff₀ ha).mp hsa
    nlinarith
  have hsin := Real.sin_pos_of_pos_of_lt_pi hy hyp
  have he1 : Real.pi*(a*s/Real.pi) = a*s := by field_simp
  have he2 : Real.pi*(x/a)*(a*s/Real.pi) = s*x := by field_simp [ha.ne']; ring
  dsimp [upperKernel, rho, cotangentRemainderIntegrand, cotangentQ, gaussianBaselineIntegrand]
  rw [he1, he2]
  field_simp [ha.ne', hs.ne', Real.pi_ne_zero, hsin.ne']
  ring

lemma integral_Ioo_add_Ioi_of_nonneg {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    (∫ s in Ioo (0 : ℝ) R, f s)+(∫ s in Ioi R, f s) = ∫ s in Ioi (0 : ℝ), f s := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have hdis : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro s hs ht
    exact not_lt.mpr hs.2 ht
  rw [← setIntegral_union hdis measurableSet_Ioi
    (hf.mono_set (fun s hs => hs.1)) (hf.mono_set (Ioi_subset_Ioi hR)),
    Ioc_union_Ioi_eq_Ioi hR]

def gaussianBaselineTailMajorant (a s : ℝ) : ℝ :=
  (1+1/Real.pi)*gaussian s+(a/Real.pi+a/3)*(s*gaussian s)+
    (a^2/(3*Real.pi))*(s^2*gaussian s)

lemma integrable_gaussianBaselineTailMajorant (a : ℝ) :
    Integrable (gaussianBaselineTailMajorant a) := by
  have h1 : Integrable (fun s : ℝ => s*gaussian s) := by
    simpa only [pow_one] using integrable_pow_gaussian 1
  exact ((integrable_gaussian.const_mul _).add (h1.const_mul _)).add
    ((integrable_pow_gaussian 2).const_mul _)

lemma abs_gaussianBaselineIntegrand_tail {a x s : ℝ} (ha : 0 < a)
    (hs : Real.pi/a ≤ s) :
    |gaussianBaselineIntegrand a x s| ≤ gaussianBaselineTailMajorant a s := by
  have hs0 : 0 < s := (div_pos Real.pi_pos ha).trans_le hs
  have has : Real.pi ≤ a*s := by
    have h := (div_le_iff₀ ha).mp hs
    nlinarith
  have hg := gaussian_nonneg s
  have h0 : |Real.cos (s*x)*gaussian s| ≤ gaussian s := by
    rw [abs_mul, abs_of_pos (gaussian_pos s)]
    exact mul_le_of_le_one_left hg (Real.abs_cos_le_one _)
  have h1 : |(a/Real.pi)*(s*Real.cos (s*x)*gaussian s)| ≤
      (a/Real.pi)*(s*gaussian s) := by
    rw [abs_mul, abs_of_pos (div_pos ha Real.pi_pos), abs_mul, abs_mul,
      abs_of_pos hs0, abs_of_pos (gaussian_pos s)]
    have h := mul_le_of_le_one_right hs0.le (Real.abs_cos_le_one (s*x))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hg)
      (div_nonneg ha.le Real.pi_pos.le)
  have h2 : |(1/a)*((Real.sin (s*x)/s)*gaussian s)| ≤
      (1/Real.pi)*gaussian s := by
    have hdiv := one_div_le_one_div_of_le Real.pi_pos has
    have hsin := Real.abs_sin_le_one (s*x)
    calc
      |(1/a)*((Real.sin (s*x)/s)*gaussian s)| =
          (1/(a*s))*|Real.sin (s*x)| * gaussian s := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr ha), abs_mul, abs_div,
          abs_of_pos hs0, abs_of_pos (gaussian_pos s)]
        ring
      _ ≤ (1/(a*s))*gaussian s := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (by positivity) hsin) hg
      _ ≤ (1/Real.pi)*gaussian s := mul_le_mul_of_nonneg_right hdiv hg
  have h3 : |(a/3)*(s*Real.sin (s*x)*gaussian s)| ≤ (a/3)*(s*gaussian s) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < a/3), abs_mul, abs_mul,
      abs_of_pos hs0, abs_of_pos (gaussian_pos s)]
    have h := mul_le_of_le_one_right hs0.le (Real.abs_sin_le_one (s*x))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hg) (by positivity)
  have h4 : |(a^2/(3*Real.pi))*(s^2*Real.sin (s*x)*gaussian s)| ≤
      (a^2/(3*Real.pi))*(s^2*gaussian s) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a^2/(3*Real.pi)), abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg s), abs_of_pos (gaussian_pos s)]
    have h := mul_le_of_le_one_right (sq_nonneg s) (Real.abs_sin_le_one (s*x))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hg) (by positivity)
  have htriangle (A B C D E : ℝ) :
      |A-B+C-D+E| ≤ |A|+|B|+|C|+|D|+|E| := by
    have hsub (v w : ℝ) : |v-w| ≤ |v|+|w| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le v (-w)
    linarith only [abs_add_le (A-B+C-D) E, hsub (A-B+C) D,
      abs_add_le (A-B) C, hsub A B]
  have ht := htriangle (Real.cos (s*x)*gaussian s)
    ((a/Real.pi)*(s*Real.cos (s*x)*gaussian s))
    ((1/a)*((Real.sin (s*x)/s)*gaussian s))
    ((a/3)*(s*Real.sin (s*x)*gaussian s))
    ((a^2/(3*Real.pi))*(s^2*Real.sin (s*x)*gaussian s))
  change |gaussianBaselineIntegrand a x s| ≤ _ at ht
  have he : gaussian s+(a/Real.pi)*(s*gaussian s)+(1/Real.pi)*gaussian s+
      (a/3)*(s*gaussian s)+(a^2/(3*Real.pi))*(s^2*gaussian s) =
        gaussianBaselineTailMajorant a s := by dsimp [gaussianBaselineTailMajorant]; ring
  rw [← he]
  linarith only [ht, h0, h1, h2, h3, h4]

lemma integral_gaussianBaselineTailMajorant_le {a : ℝ} (ha : 0 < a) :
    a/Real.pi*(∫ s in Ioi (Real.pi/a), gaussianBaselineTailMajorant a s) ≤
      (a^2*(2/Real.pi^2+1/Real.pi^3+2/(3*Real.pi)+a^2/(3*Real.pi^3)))*
        gaussian (Real.pi/a) := by
  have hR : 0 < Real.pi/a := div_pos Real.pi_pos ha
  have h0 := gaussianTailMoment_zero_le hR
  have h1 := gaussianTailMoment_one (Real.pi/a)
  have h2 := gaussianTailMoment_two_le hR
  have hi1 : IntegrableOn (fun s : ℝ => s*gaussian s) (Ioi (Real.pi/a)) := by
    simpa only [pow_one] using (integrable_pow_gaussian 1).integrableOn
  have hi01 : IntegrableOn (fun s : ℝ => (1+1/Real.pi)*gaussian s+
      (a/Real.pi+a/3)*(s*gaussian s)) (Ioi (Real.pi/a)) :=
    (integrable_gaussian.integrableOn.const_mul _).add (hi1.const_mul _)
  have hint : (∫ s in Ioi (Real.pi/a), gaussianBaselineTailMajorant a s) =
      (1+1/Real.pi)*gaussianTailMoment 0 (Real.pi/a)+
      (a/Real.pi+a/3)*gaussianTailMoment 1 (Real.pi/a)+
      (a^2/(3*Real.pi))*gaussianTailMoment 2 (Real.pi/a) := by
    unfold gaussianBaselineTailMajorant
    rw [integral_add hi01
        ((integrable_pow_gaussian 2).integrableOn.const_mul (a^2/(3*Real.pi))),
      integral_add (integrable_gaussian.integrableOn.const_mul (1+1/Real.pi))
        (hi1.const_mul (a/Real.pi+a/3)),
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [gaussianTailMoment, pow_zero, pow_one, one_mul]
  rw [hint, h1]
  have h0' := mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 1+1/Real.pi)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ a^2/(3*Real.pi))
  have hsum : (1+1/Real.pi)*gaussianTailMoment 0 (Real.pi/a)+
      (a/Real.pi+a/3)*gaussian (Real.pi/a)+
      (a^2/(3*Real.pi))*gaussianTailMoment 2 (Real.pi/a) ≤
      (1+1/Real.pi)*(gaussian (Real.pi/a)/(Real.pi/a))+
      (a/Real.pi+a/3)*gaussian (Real.pi/a)+
      (a^2/(3*Real.pi))*((Real.pi/a+1/(Real.pi/a))*gaussian (Real.pi/a)) := by
    linarith only [h0', h2']
  have hm := mul_le_mul_of_nonneg_left hsum (div_nonneg ha.le Real.pi_pos.le)
  convert hm using 1 <;> field_simp [ha.ne', Real.pi_ne_zero] <;> ring

lemma abs_gaussianBaseline_tail_le {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1/2) :
    |a/Real.pi*(∫ s in Ioi (Real.pi/a), gaussianBaselineIntegrand a x s)| ≤
      gaussian (1/a) := by
  have hi := (integrable_gaussianBaselineIntegrand a x).integrableOn (s := Ioi (Real.pi/a))
  have hm := (integrable_gaussianBaselineTailMajorant a).integrableOn (s := Ioi (Real.pi/a))
  have habs : |∫ s in Ioi (Real.pi/a), gaussianBaselineIntegrand a x s| ≤
      ∫ s in Ioi (Real.pi/a), gaussianBaselineTailMajorant a s := by
    apply le_trans abs_integral_le_integral_abs
    apply integral_mono_ae hi.abs hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact abs_gaussianBaselineIntegrand_tail ha (show Real.pi/a < s from hs).le
  have hp1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hp2 : (1 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp3 : (1 : ℝ) ≤ Real.pi^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 Real.pi_pos.le, Real.pi_gt_three]
  have hc1 : (2 : ℝ)/Real.pi^2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    linarith
  have hc2 : (1 : ℝ)/Real.pi^3 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos Real.pi_pos 3)).2
    linarith
  have hc3 : (2 : ℝ)/(3*Real.pi) ≤ 2/3 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3*Real.pi)).2
    linarith
  have hc4 : a^2/(3*Real.pi^3) ≤ 1/3 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3*Real.pi^3)).2
    nlinarith
  have hc : a^2*(2/Real.pi^2+1/Real.pi^3+2/(3*Real.pi)+a^2/(3*Real.pi^3)) ≤ 1 := by
    have hsum : 2/Real.pi^2+1/Real.pi^3+2/(3*Real.pi)+a^2/(3*Real.pi^3) ≤ 4 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg a)
    nlinarith
  have hg : gaussian (Real.pi/a) ≤ gaussian (1/a) := by
    apply gaussian_antitoneOn
      (show (1/a : ℝ) ∈ Ici 0 from (by positivity : (0 : ℝ) ≤ 1/a))
      (show (Real.pi/a : ℝ) ∈ Ici 0 from (by positivity : (0 : ℝ) ≤ Real.pi/a))
    exact div_le_div_of_nonneg_right hp1 ha.le
  rw [abs_mul, abs_of_pos (div_pos ha Real.pi_pos)]
  calc
    a/Real.pi*|∫ s in Ioi (Real.pi/a), gaussianBaselineIntegrand a x s| ≤
        a/Real.pi*(∫ s in Ioi (Real.pi/a), gaussianBaselineTailMajorant a s) :=
      mul_le_mul_of_nonneg_left habs (div_nonneg ha.le Real.pi_pos.le)
    _ ≤ (a^2*(2/Real.pi^2+1/Real.pi^3+2/(3*Real.pi)+a^2/(3*Real.pi^3)))*
        gaussian (Real.pi/a) := integral_gaussianBaselineTailMajorant_le ha
    _ ≤ gaussian (Real.pi/a) := mul_le_of_le_one_left (gaussian_nonneg _) hc
    _ ≤ gaussian (1/a) := hg

def scaledGaussianKernelIntegral (a x : ℝ) : ℝ :=
  a/Real.pi * ∫ s in Ioo (0 : ℝ) (Real.pi/a),
    upperKernel (x/a) (a*s/Real.pi)*gaussian s

lemma scaledGaussianKernelIntegral_eq {a x : ℝ} (ha : 0 < a) :
    scaledGaussianKernelIntegral a x = gaussianBaselineValue a x -
      a/Real.pi*(∫ s in Ioi (Real.pi/a), gaussianBaselineIntegrand a x s) +
        cotangentRemainderIntegral a x := by
  have hi := integrable_gaussianBaselineIntegrand a x
  have hq := integrableOn_cotangentRemainderIntegrand (x := x) ha
  have hfinite : (∫ s in Ioo (0 : ℝ) (Real.pi/a),
      upperKernel (x/a) (a*s/Real.pi)*gaussian s) =
      (∫ s in Ioo (0 : ℝ) (Real.pi/a), gaussianBaselineIntegrand a x s) +
      (∫ s in Ioo (0 : ℝ) (Real.pi/a), cotangentRemainderIntegrand a x s) := by
    calc
      _ = ∫ s in Ioo (0 : ℝ) (Real.pi/a),
          gaussianBaselineIntegrand a x s+cotangentRemainderIntegrand a x s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact gaussian_kernel_decomposition ha hs.1 hs.2
      _ = _ := integral_add hi.integrableOn hq
  have hsplit := integral_Ioo_add_Ioi_of_nonneg
    (f := gaussianBaselineIntegrand a x) (div_nonneg Real.pi_pos.le ha.le) hi.integrableOn
  have hmul := congrArg (fun t : ℝ => a/Real.pi*t) hsplit
  have hfull := integral_gaussianBaselineIntegrand ha.ne' x
  dsimp only at hmul
  rw [hfull] at hmul
  dsimp [scaledGaussianKernelIntegral, cotangentRemainderIntegral]
  rw [hfinite]
  nlinarith only [hmul]

lemma scaledGaussianKernelIntegral_le {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1/2) :
    scaledGaussianKernelIntegral a x ≤ gaussianBaselineValue a x+
      a^4/(15*Real.pi)+(1+a^2/(2*Real.pi))*gaussian (1/a) := by
  rw [scaledGaussianKernelIntegral_eq ha]
  have ht := (abs_le.mp (abs_gaussianBaseline_tail_le (x := x) ha ha2)).1
  have hq := (le_abs_self (cotangentRemainderIntegral a x)).trans
    (abs_cotangentRemainderIntegral_le ha)
  nlinarith only [ht, hq]

end KellerKlein
