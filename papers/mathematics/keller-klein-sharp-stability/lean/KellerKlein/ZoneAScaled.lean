import KellerKlein.KernelMeasurability
import KellerKlein.ZoneAProfile

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

def holderProfile (a b ξ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, upperKernel ξ u * cosineProfile b (Real.pi * u / a)

def scaledProfile (a b ξ s : ℝ) : ℝ :=
  upperKernel ξ (a * s / Real.pi) * cosineProfile b s

lemma holderProfile_eq_scaled {a : ℝ} (ha : a ≠ 0) (b ξ : ℝ) :
    holderProfile a b ξ = a / Real.pi * ∫ s in (0 : ℝ)..(Real.pi / a), scaledProfile a b ξ s := by
  have h := intervalIntegral.integral_comp_mul_left (scaledProfile a b ξ)
    (a := (0 : ℝ)) (b := 1) (c := Real.pi / a) (div_ne_zero Real.pi_ne_zero ha)
  have he : (fun u => scaledProfile a b ξ (Real.pi / a * u)) =
      (fun u => upperKernel ξ u * cosineProfile b (Real.pi * u / a)) := by
    funext u
    unfold scaledProfile
    have h1 : a * (Real.pi / a * u) / Real.pi = u := by field_simp [ha, Real.pi_ne_zero]
    have h2 : Real.pi / a * u = Real.pi * u / a := by ring
    rw [h1, h2]
  rw [he] at h
  simpa only [holderProfile, mul_zero, mul_one, smul_eq_mul, inv_div] using h

lemma intervalIntegrable_scaledProfile {a : ℝ} (ha : a ≠ 0) (b ξ : ℝ) :
    IntervalIntegrable (scaledProfile a b ξ) volume 0 (Real.pi / a) := by
  have h := (intervalIntegrable_upperKernel_cosineProfile a b ξ).comp_mul_left (a / Real.pi)
  have he : (fun s => upperKernel ξ (a / Real.pi * s) *
      cosineProfile b (Real.pi * (a / Real.pi * s) / a)) = scaledProfile a b ξ := by
    funext s
    have h1 : a / Real.pi * s = a * s / Real.pi := by ring
    have h2 : Real.pi * (a / Real.pi * s) / a = s := by field_simp [ha, Real.pi_ne_zero]
    rw [h2, h1]
    rfl
  rw [he] at h
  simpa only [zero_div, one_div, inv_div] using h

lemma intervalIntegrable_scaledProfile_subinterval {a L R : ℝ} (ha : 0 < a) (b ξ : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hR : R ≤ Real.pi / a) :
    IntervalIntegrable (scaledProfile a b ξ) volume L R := by
  apply (intervalIntegrable_scaledProfile ha.ne' b ξ).mono _ le_rfl
  rw [uIcc_of_le hLR, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / a)]
  intro s hs
  exact ⟨hL.trans hs.1, hs.2.trans hR⟩

lemma continuous_primaryPolynomial (a b ξ : ℝ) : Continuous (primaryPolynomial a b ξ) := by
  unfold primaryPolynomial upperPoly lowerPoly
  fun_prop

lemma scaled_primary_bound {a b ξ S : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) (hS0 : 0 ≤ S)
    (hSa : S ≤ Real.pi / a) (hSb : S ≤ Real.pi / (2 * b)) :
    a / Real.pi * (∫ s in (0 : ℝ)..S, scaledProfile a b ξ s) ≤
      a / Real.pi * (∫ s in Ioc (0 : ℝ) S, gaussian s * primaryPolynomial a b ξ s) := by
  have hp : Continuous (fun s => gaussian s * primaryPolynomial a b ξ s) :=
    continuous_gaussian.mul (continuous_primaryPolynomial a b ξ)
  have hf := intervalIntegrable_scaledProfile_subinterval ha b ξ le_rfl hS0 hSa
  have hi : (∫ s in (0 : ℝ)..S, scaledProfile a b ξ s) ≤
      ∫ s in (0 : ℝ)..S, gaussian s * primaryPolynomial a b ξ s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hS0 hf (hp.intervalIntegrable 0 S)
    intro s hs
    have has : a * s < Real.pi := by
      have h := (lt_div_iff₀ ha).1 (hs.2.trans_le hSa)
      simpa [mul_comm] using h
    have hbs : b * s ≤ Real.pi / 2 := by
      have h := (le_div_iff₀ (mul_pos (by norm_num) hb)).1 (hs.2.le.trans hSb)
      nlinarith only [h]
    exact primary_profile_bound ha hb hξ hξ1 hs.1 has hbs
  simp only [intervalIntegral.integral_of_le hS0] at hi ⊢
  exact mul_le_mul_of_nonneg_left hi (by positivity)

lemma gaussian_profile_bound {a b ξ s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) (hs : 0 < s)
    (has : a * s < Real.pi) (hbs : b * s ≤ Real.pi / 2) :
    scaledProfile a b ξ s ≤ gaussian s * primaryPolynomial a 0 ξ s := by
  have hu : 0 < a * s / Real.pi := by positivity
  have hu1 : a * s / Real.pi < 1 := (div_lt_one Real.pi_pos).2 has
  have hk0 := upperKernel_nonneg hξ hξ1 hu hu1
  have hkU := upperKernel_le_upperPoly hξ hξ1 hu hu1
  have hy : Real.pi * (a * s / Real.pi) = a * s := by field_simp
  rw [hy] at hkU
  have hp : cosineProfile b s ≤ gaussian s := by
    have h := cosine_profile_le_quartic hb hs.le hbs
    have he : Real.exp (-(s ^ 2 / 2) - b ^ 2 * s ^ 4 / 12) ≤ gaussian s := by
      unfold gaussian
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ b ^ 2 * s ^ 4 / 12 := by positivity
      linarith only [hn]
    exact h.trans he
  have h1 := mul_le_mul_of_nonneg_left hp hk0
  have h2 := mul_le_mul_of_nonneg_right hkU (gaussian_nonneg s)
  simp only [primaryPolynomial, zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 4 ≠ 0),
    zero_mul, zero_div, sub_zero, zero_add, add_zero]
  unfold scaledProfile
  nlinarith only [h1, h2]

lemma scaled_primary_gaussian_bound {a b ξ S : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) (hS0 : 0 ≤ S)
    (hSa : S ≤ Real.pi / a) (hSb : S ≤ Real.pi / (2 * b)) :
    a / Real.pi * (∫ s in (0 : ℝ)..S, scaledProfile a b ξ s) ≤
      a / Real.pi * (∫ s in Ioc (0 : ℝ) S, gaussian s * primaryPolynomial a 0 ξ s) := by
  have hp : Continuous (fun s => gaussian s * primaryPolynomial a 0 ξ s) :=
    continuous_gaussian.mul (continuous_primaryPolynomial a 0 ξ)
  have hf := intervalIntegrable_scaledProfile_subinterval ha b ξ le_rfl hS0 hSa
  have hi : (∫ s in (0 : ℝ)..S, scaledProfile a b ξ s) ≤
      ∫ s in (0 : ℝ)..S, gaussian s * primaryPolynomial a 0 ξ s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hS0 hf (hp.intervalIntegrable 0 S)
    intro s hs
    have has : a * s < Real.pi := by
      have h := (lt_div_iff₀ ha).1 (hs.2.trans_le hSa)
      simpa [mul_comm] using h
    have hbs : b * s ≤ Real.pi / 2 := by
      have h := (le_div_iff₀ (mul_pos (by norm_num) hb)).1 (hs.2.le.trans hSb)
      nlinarith only [h]
    exact gaussian_profile_bound ha hb hξ hξ1 hs.1 has hbs
  simp only [intervalIntegral.integral_of_le hS0] at hi ⊢
  exact mul_le_mul_of_nonneg_left hi (by positivity)

end KellerKlein.ZoneA
