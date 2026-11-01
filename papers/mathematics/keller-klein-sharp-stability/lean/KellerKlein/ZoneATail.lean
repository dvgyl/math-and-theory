import KellerKlein.ZoneAIntegral
import KellerKlein.ZoneAConstants

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

lemma polynomial_gaussian_tail {a S : ℝ} (ha : 0 < a) (hS : 1 / a ≤ S)
    (k n : ℕ) :
    (∫ s in Ioi S, s ^ k * gaussian s) ≤ a ^ n * halfMoment (k + n) := by
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ 1 / a).trans hS
  have hsub : Ioi S ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_le_of_lt hS0 hs
  have hf := (integrable_pow_gaussian k).integrableOn (s := Ioi S)
  have hg := ((integrable_pow_gaussian (k + n)).const_mul (a ^ n)).integrableOn
    (s := Ioi S)
  have hfirst : (∫ s in Ioi S, s ^ k * gaussian s) ≤
      ∫ s in Ioi S, a ^ n * (s ^ (k + n) * gaussian s) := by
    apply setIntegral_mono_on hf hg measurableSet_Ioi
    intro s hs
    have hs0 : 0 ≤ s := (hsub hs).le
    have has : 1 ≤ a * s := by
      have h := (div_le_iff₀ ha).1 (hS.trans hs.le)
      simpa [mul_comm] using h
    have hp : (1 : ℝ) ≤ (a * s) ^ n := one_le_pow₀ has
    have hm := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (pow_nonneg hs0 k) (gaussian_nonneg s))
    calc
      s ^ k * gaussian s = 1 * (s ^ k * gaussian s) := by ring
      _ ≤ (a * s) ^ n * (s ^ k * gaussian s) := hm
      _ = a ^ n * (s ^ (k + n) * gaussian s) := by rw [mul_pow, pow_add]; ring
  have hsecond : (∫ s in Ioi S, a ^ n * (s ^ (k + n) * gaussian s)) ≤
      ∫ s in Ioi (0 : ℝ), a ^ n * (s ^ (k + n) * gaussian s) := by
    apply setIntegral_mono_set ((integrableOn_pow_gaussian (k + n)).const_mul (a ^ n))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (pow_nonneg ha.le n)
        (mul_nonneg (pow_nonneg hs.le (k + n)) (gaussian_nonneg s))
    · exact Filter.Eventually.of_forall hsub
  calc
    (∫ s in Ioi S, s ^ k * gaussian s) ≤
        ∫ s in Ioi S, a ^ n * (s ^ (k + n) * gaussian s) := hfirst
    _ ≤ ∫ s in Ioi (0 : ℝ), a ^ n * (s ^ (k + n) * gaussian s) := hsecond
    _ = a ^ n * halfMoment (k + n) := by rw [integral_const_mul]; rfl

def negativePolynomial (a b ξ s : ℝ) : ℝ :=
  (a / Real.pi) * s + A ξ * a ^ 2 * s ^ 2 + b ^ 2 * (1 + ξ) * s ^ 4 / 12

lemma A_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ A ξ := by unfold A; positivity
lemma AL_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ AL ξ := by unfold AL; positivity
lemma B_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ B ξ := by unfold B; positivity
lemma C_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ C ξ := by unfold C; positivity
lemma D_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ D ξ := by unfold D; positivity

lemma primaryPolynomial_ge_neg {a b ξ s : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (hs : 0 ≤ s) : -negativePolynomial a b ξ s ≤ primaryPolynomial a b ξ s := by
  have hA := A_nonneg hξ
  have hAL := AL_nonneg hξ
  have hB := B_nonneg hξ
  have hC := C_nonneg hξ
  have hD := D_nonneg hξ
  have hnonneg : 0 ≤ 1 + ξ + B ξ * (a * s) ^ 3 + C ξ * (a * s) ^ 4 +
      D ξ * (a * s) ^ 7 + b ^ 2 * s ^ 4 / 12 * (a * s / Real.pi) +
      b ^ 2 * s ^ 4 / 12 * AL ξ * (a * s) ^ 2 +
      b ^ 4 * s ^ 8 / 288 * (1 + ξ) := by positivity
  apply le_of_sub_nonneg
  convert hnonneg using 1
  unfold negativePolynomial primaryPolynomial upperPoly lowerPoly
  ring

lemma integrable_negativePolynomial (a b ξ : ℝ) :
    Integrable (fun s => negativePolynomial a b ξ s * gaussian s) := by
  have h1 := (integrable_pow_gaussian 1).const_mul (a / Real.pi)
  have h2 := (integrable_pow_gaussian 2).const_mul (A ξ * a ^ 2)
  have h4 := (integrable_pow_gaussian 4).const_mul (b ^ 2 * (1 + ξ) / 12)
  convert (h1.add h2).add h4 using 1
  funext s
  simp only [Pi.add_apply]
  unfold negativePolynomial
  ring

lemma primary_truncation {a b ξ S : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ) (hS : 0 ≤ S) :
    (∫ s in Ioc (0 : ℝ) S, gaussian s * primaryPolynomial a b ξ s) ≤
      (∫ s in Ioi (0 : ℝ), gaussian s * primaryPolynomial a b ξ s) +
      ∫ s in Ioi S, negativePolynomial a b ξ s * gaussian s := by
  have hsub : Ioi S ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_le_of_lt hS hs
  have hp := integrable_primaryPolynomial a b ξ
  have hn := (integrable_negativePolynomial a b ξ).integrableOn (s := Ioi S)
  have hdiff := integral_diff (f := fun s => gaussian s * primaryPolynomial a b ξ s)
    measurableSet_Ioi hp hsub
  rw [Ioi_diff_Ioi] at hdiff
  have htail : -(∫ s in Ioi S, negativePolynomial a b ξ s * gaussian s) ≤
      ∫ s in Ioi S, gaussian s * primaryPolynomial a b ξ s := by
    rw [← integral_neg]
    apply setIntegral_mono_on hn.neg (hp.mono_set hsub) measurableSet_Ioi
    intro s hs
    have h := mul_le_mul_of_nonneg_right
      (primaryPolynomial_ge_neg (b := b) ha hξ (hsub hs).le) (gaussian_nonneg s)
    change -(negativePolynomial a b ξ s * gaussian s) ≤ gaussian s * primaryPolynomial a b ξ s
    convert h using 1 <;> ring
  rw [hdiff]
  linarith

lemma negativePolynomial_tail {a b ξ S : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ)
    (hS : 1 / a ≤ S) :
    (∫ s in Ioi S, negativePolynomial a b ξ s * gaussian s) ≤
      48 * a ^ 7 / Real.pi + 105 * Real.pi * phi0 * A ξ * a ^ 8 +
      945 * Real.pi * phi0 * b ^ 2 * (1 + ξ) * a ^ 6 / 12 := by
  have h10 : halfMoment 10 = 945 * Real.pi * phi0 := by
    have h := halfMoment_add_two 8
    norm_num [halfMoment_eight] at h
    nlinarith only [h]
  have h1 := polynomial_gaussian_tail ha hS 1 6
  have h2 := polynomial_gaussian_tail ha hS 2 6
  have h4 := polynomial_gaussian_tail ha hS 4 6
  norm_num [halfMoment_seven, halfMoment_eight, h10] at h1 h2 h4
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ a / Real.pi)
  have h2' := mul_le_mul_of_nonneg_left h2 (mul_nonneg (A_nonneg hξ) (sq_nonneg a))
  have h4' := mul_le_mul_of_nonneg_left h4
    (by positivity : 0 ≤ b ^ 2 * (1 + ξ) / 12)
  have he : (fun s => negativePolynomial a b ξ s * gaussian s) =
      (fun s => (a / Real.pi) * (s ^ 1 * gaussian s) +
        (A ξ * a ^ 2) * (s ^ 2 * gaussian s) +
        (b ^ 2 * (1 + ξ) / 12) * (s ^ 4 * gaussian s)) := by
    funext s
    unfold negativePolynomial
    ring
  rw [he, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · simp only [pow_one]
    convert add_le_add (add_le_add h1' h2') h4' using 1 <;> ring
  · exact ((integrable_pow_gaussian 1).const_mul _).integrableOn
  · exact ((integrable_pow_gaussian 2).const_mul _).integrableOn
  · exact (((integrable_pow_gaussian 1).const_mul _).add
      ((integrable_pow_gaussian 2).const_mul _)).integrableOn
  · exact ((integrable_pow_gaussian 4).const_mul _).integrableOn

end KellerKlein.ZoneA
