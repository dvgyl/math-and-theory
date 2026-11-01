import KellerKlein.ZoneATail

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

lemma primary_extension_error {a b ξ S : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hS : 1 / a ≤ S) :
    a / Real.pi * (∫ s in Ioi S, negativePolynomial a b ξ s * gaussian s) ≤
      66 * a ^ 8 := by
  have he := mul_le_mul_of_nonneg_left (negativePolynomial_tail (b := b) ha hξ hS)
    (by positivity : 0 ≤ a / Real.pi)
  have hcoeff1 : 48 / Real.pi ^ 2 ≤ (16 : ℝ) / 3 := by
    apply (div_le_iff₀ (pow_pos Real.pi_pos 2)).2
    nlinarith [pi_sq_lower]
  have hφA : phi0 * A ξ ≤ (2 / 5 : ℝ) * (5 / 16) :=
    mul_le_mul phi0_upper (A_bound hξ hξ1) (A_nonneg hξ) (by norm_num)
  have hφξ : phi0 * (1 + ξ) ≤ (2 / 5 : ℝ) * (3 / 2) :=
    mul_le_mul phi0_upper (by linarith) (by linarith) (by norm_num)
  have h9 : a ^ 9 ≤ a ^ 8 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have hb2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb hba 2
  have hb7 : b ^ 2 * a ^ 7 ≤ a ^ 9 := by
    convert mul_le_mul_of_nonneg_right hb2 (pow_nonneg ha.le 7) using 1 <;> ring
  have ht1 := mul_le_mul_of_nonneg_right hcoeff1 (pow_nonneg ha.le 8)
  have ht2 := mul_le_mul (show 105 * phi0 * A ξ ≤ (105 : ℝ) / 8 by nlinarith only [hφA])
    h9 (pow_nonneg ha.le 9) (by norm_num : 0 ≤ (105 : ℝ) / 8)
  have ht3 := mul_le_mul
    (show 945 / 12 * phi0 * (1 + ξ) ≤ (189 : ℝ) / 4 by nlinarith only [hφξ])
    (hb7.trans h9) (mul_nonneg (sq_nonneg b) (pow_nonneg ha.le 7))
    (by norm_num : 0 ≤ (189 : ℝ) / 4)
  have halg : a / Real.pi *
      (48 * a ^ 7 / Real.pi + 105 * Real.pi * phi0 * A ξ * a ^ 8 +
        945 * Real.pi * phi0 * b ^ 2 * (1 + ξ) * a ^ 6 / 12) =
      (48 / Real.pi ^ 2) * a ^ 8 + (105 * phi0 * A ξ) * a ^ 9 +
        (945 / 12 * phi0 * (1 + ξ)) * (b ^ 2 * a ^ 7) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [halg] at he
  have hsum := add_le_add (add_le_add ht1 ht2) ht3
  have h66 : ((16 : ℝ) / 3) * a ^ 8 + (105 / 8) * a ^ 8 + (189 / 4) * a ^ 8 ≤
      66 * a ^ 8 := by nlinarith [pow_nonneg ha.le 8]
  exact he.trans (hsum.trans h66)

lemma primary_truncated_integral_bound {a b ξ S : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hS : 1 / a ≤ S) :
    a / Real.pi * (∫ s in Ioc (0 : ℝ) S, gaussian s * primaryPolynomial a b ξ s) ≤
      primaryValue a b ξ + 128 * a ^ 8 := by
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ 1 / a).trans hS
  have ht := mul_le_mul_of_nonneg_left
    (primary_truncation (b := b) ha.le hξ hS0) (by positivity : 0 ≤ a / Real.pi)
  rw [mul_add, integral_primaryPolynomial_eq] at ht
  have he := primary_extension_error ha ha1 hb hba hξ hξ1 hS
  nlinarith [pow_nonneg ha.le 8]

end KellerKlein.ZoneA
