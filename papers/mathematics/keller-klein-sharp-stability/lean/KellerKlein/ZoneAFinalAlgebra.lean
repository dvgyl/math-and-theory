import KellerKlein.ZoneATailBound
import KellerKlein.ZoneAAliasIntegral
import KellerKlein.GaussianTarget

noncomputable section

namespace KellerKlein.ZoneA

def targetLower (a ξ : ℝ) : ℝ :=
  phi0 * a * (1 + ξ) - phi0 * a ^ 3 * (1 + ξ ^ 3) / 6

lemma targetLower_le_c_pair {a ξ : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ) :
    targetLower a ξ ≤ c a + c (ξ * a) := c_pair_lower ha hξ

lemma quartic_coefficient_bound {θ ξ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    ξ ^ 2 + 2 * ξ / 3 + 2 * θ ^ 2 / 3 ≤ 5 / 4 := by
  have h2 := pow_le_pow_left₀ hξ hξ1 2
  have ht2 := pow_le_pow_left₀ hθ hθ1 2
  norm_num at h2
  norm_num only [one_pow] at ht2
  nlinarith only [h2, ht2, hξ1]

lemma fifth_coefficient_bound {θ ξ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    3 * C ξ + 5 * AL ξ * θ ^ 2 / 4 + 35 * (1 + ξ) * θ ^ 4 / 96 ≤ 1371 / 1280 := by
  have ht2 := pow_le_pow_left₀ hθ hθ1 2
  have ht4 := pow_le_pow_left₀ hθ hθ1 4
  norm_num only [one_pow] at ht2 ht4
  have hAL := mul_le_mul (AL_bound hξ hξ1) ht2 (sq_nonneg θ)
    (by norm_num : 0 ≤ (19 : ℝ) / 48)
  have hξθ := mul_le_mul (show 1 + ξ ≤ 3 / 2 by linarith) ht4
    (pow_nonneg hθ 4) (by norm_num : 0 ≤ (3 : ℝ) / 2)
  nlinarith only [C_bound hξ hξ1, hAL, hξθ]

lemma eighth_coefficient_bound {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    2 * ξ ^ 5 / 15 ≤ (1 : ℝ) / 240 := by
  have h5 := pow_le_pow_left₀ hξ hξ1 5
  norm_num at h5
  nlinarith only [h5]

lemma aliasHigh_linear_bound {a ξ : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ) :
    aliasHigh a ξ ≤ a ^ 2 / Real.pi ^ 2 + phi0 * a ^ 3 * (ξ + 1 / 3) * ξ +
      3 * phi0 * a ^ 5 / Real.pi ^ 4 := by
  have hφ := phi0_pos
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi * ξ))
    (by positivity : 0 ≤ a ^ 2 / Real.pi ^ 2)
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le (mul_nonneg Real.pi_pos.le hξ))
    (by positivity : 0 ≤ phi0 * a ^ 3 * (ξ + 1 / 3) / Real.pi)
  have hsin1 := mul_le_mul_of_nonneg_left (Real.sin_le_one (Real.pi * ξ))
    (by positivity : 0 ≤ 3 * phi0 * a ^ 5 / Real.pi ^ 4)
  unfold aliasHigh
  convert add_le_add (add_le_add hcos hsin) hsin1 using 1 <;>
    field_simp [Real.pi_ne_zero] <;> ring

lemma aliasHigh_third_constant_bound {a ξ : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) :
    aliasHigh a ξ / 3 ≤ a ^ 2 / (3 * Real.pi ^ 2) +
      5 * phi0 * a ^ 3 / (18 * Real.pi) + phi0 * a ^ 5 / Real.pi ^ 4 := by
  have hφ := phi0_pos
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi * ξ))
    (by positivity : 0 ≤ a ^ 2 / Real.pi ^ 2)
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one (Real.pi * ξ))
    (by positivity : 0 ≤ phi0 * a ^ 3 * (ξ + 1 / 3) / Real.pi)
  have hsin1 := mul_le_mul_of_nonneg_left (Real.sin_le_one (Real.pi * ξ))
    (by positivity : 0 ≤ 3 * phi0 * a ^ 5 / Real.pi ^ 4)
  have hξterm := mul_le_mul_of_nonneg_left (show ξ + 1 / 3 ≤ 5 / 6 by linarith)
    (by positivity : 0 ≤ phi0 * a ^ 3 / Real.pi)
  unfold aliasHigh
  ring_nf at hcos hsin hsin1 hξterm ⊢
  linarith only [hcos, hsin, hsin1, hξterm]

lemma high_algebra_margin {a θ ξ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 7 / 100)
    (hθ : 19 / 20 ≤ θ) (hθ1 : θ ≤ 1) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    primaryValue a (θ * a) ξ + aliasHigh a ξ + 128 * a ^ 8 ≤
      targetLower a ξ - a ^ 3 / 200 := by
  have hφ := phi0_pos
  have hθ0 : 0 ≤ θ := by linarith
  have ht2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 20) hθ 2
  norm_num at ht2
  have hθneg := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ 1 + ξ by linarith)
  have hcubic : 1 / 6 + ξ ^ 2 / 2 - θ ^ 2 * (1 + ξ) / 4 ≤ -449 / 9600 := by
    have h := high_theta_cubic_bound hξ hξ1
    nlinarith only [h, hθneg]
  have h3 := mul_le_mul_of_nonneg_left hcubic (by positivity : 0 ≤ phi0 * a ^ 3)
  have h4 := mul_le_mul_of_nonneg_left (quartic_coefficient_bound hθ0 hθ1 hξ hξ1)
    (by positivity : 0 ≤ a ^ 4 / Real.pi ^ 2)
  have h5 := mul_le_mul_of_nonneg_left
    (add_le_add_right (fifth_coefficient_bound hθ0 hθ1 hξ hξ1) (3 / Real.pi ^ 4))
    (by positivity : 0 ≤ phi0 * a ^ 5)
  have h8c := mul_le_mul_of_nonneg_right (eighth_coefficient_bound hξ hξ1)
    (by positivity : 0 ≤ 1 / Real.pi ^ 2)
  have h8 := mul_le_mul_of_nonneg_left (add_le_add_left h8c 128)
    (pow_nonneg ha 8)
  have hsum := add_le_add (add_le_add (add_le_add h3 h4) h5) h8
  have hn := mul_le_mul_of_nonneg_right (high_theta_numerical_margin ha ha1) (pow_nonneg ha 3)
  have halias := aliasHigh_linear_bound ha hξ
  have hleft : primaryValue a (θ * a) ξ +
      (a ^ 2 / Real.pi ^ 2 + phi0 * a ^ 3 * (ξ + 1 / 3) * ξ +
        3 * phi0 * a ^ 5 / Real.pi ^ 4) + 128 * a ^ 8 - targetLower a ξ =
      phi0 * a ^ 3 * (1 / 6 + ξ ^ 2 / 2 - θ ^ 2 * (1 + ξ) / 4) +
      (a ^ 4 / Real.pi ^ 2) * (ξ ^ 2 + 2 * ξ / 3 + 2 * θ ^ 2 / 3) +
      phi0 * a ^ 5 * (3 * C ξ + 5 * AL ξ * θ ^ 2 / 4 +
        35 * (1 + ξ) * θ ^ 4 / 96 + 3 / Real.pi ^ 4) +
      a ^ 8 * (128 + (2 * ξ ^ 5 / 15) * (1 / Real.pi ^ 2)) := by
    unfold primaryValue targetLower A B D
    field_simp [Real.pi_ne_zero]
    ring
  have hright : phi0 * a ^ 3 * (-449 / 9600) +
      (a ^ 4 / Real.pi ^ 2) * (5 / 4) +
      phi0 * a ^ 5 * (1371 / 1280 + 3 / Real.pi ^ 4) +
      a ^ 8 * (128 + (1 / 240) * (1 / Real.pi ^ 2)) =
      (-(449 / 9600 : ℝ) * phi0 + 5 / (4 * Real.pi ^ 2) * a +
        phi0 * (1371 / 1280 + 3 / Real.pi ^ 4) * a ^ 2 +
        (128 + 1 / (240 * Real.pi ^ 2)) * a ^ 5) * a ^ 3 := by ring
  rw [← hleft, hright] at hsum
  linarith only [halias, hsum, hn]

lemma low_algebra_margin {a ξ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 7 / 100)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    primaryValue a 0 ξ + aliasHigh a ξ / 3 + 128 * a ^ 8 ≤
      targetLower a ξ - a ^ 2 / 20 := by
  have hφ := phi0_pos
  have hξ2 := pow_le_pow_left₀ hξ hξ1 2
  norm_num at hξ2
  have hquartic : ξ ^ 2 + 2 * ξ / 3 ≤ 7 / 12 := by nlinarith only [hξ2, hξ1]
  have h4 := mul_le_mul_of_nonneg_left hquartic (by positivity : 0 ≤ a ^ 4 / Real.pi ^ 2)
  have hC : 3 * C ξ ≤ (113 : ℝ) / 3840 := by nlinarith only [C_bound hξ hξ1]
  have h5 := mul_le_mul_of_nonneg_left (add_le_add_right hC (1 / Real.pi ^ 4))
    (by positivity : 0 ≤ phi0 * a ^ 5)
  have h8c := mul_le_mul_of_nonneg_right (eighth_coefficient_bound hξ hξ1)
    (by positivity : 0 ≤ 1 / Real.pi ^ 2)
  have h8 := mul_le_mul_of_nonneg_left (add_le_add_left h8c 128) (pow_nonneg ha 8)
  have hcubic : 1 / 6 - ξ ^ 2 / 2 - ξ / 3 + 5 / (18 * Real.pi) ≤
      1 / 6 + 5 / (18 * Real.pi) := by nlinarith [sq_nonneg ξ]
  have h3 := mul_le_mul_of_nonneg_left hcubic (by positivity : 0 ≤ phi0 * a ^ 3)
  have hsum := add_le_add (add_le_add (add_le_add h3 h4) h5) h8
  have hn := mul_le_mul_of_nonneg_right (low_theta_numerical_margin ha ha1) (sq_nonneg a)
  have halias := aliasHigh_third_constant_bound ha hξ hξ1
  have hleft : primaryValue a 0 ξ +
      (a ^ 2 / (3 * Real.pi ^ 2) + 5 * phi0 * a ^ 3 / (18 * Real.pi) +
        phi0 * a ^ 5 / Real.pi ^ 4) + 128 * a ^ 8 - targetLower a ξ =
      -(2 * a ^ 2 / (3 * Real.pi ^ 2)) +
      phi0 * a ^ 3 * (1 / 6 - ξ ^ 2 / 2 - ξ / 3 + 5 / (18 * Real.pi)) +
      (a ^ 4 / Real.pi ^ 2) * (ξ ^ 2 + 2 * ξ / 3) +
      phi0 * a ^ 5 * (3 * C ξ + 1 / Real.pi ^ 4) +
      a ^ 8 * (128 + (2 * ξ ^ 5 / 15) * (1 / Real.pi ^ 2)) := by
    unfold primaryValue targetLower A B D
    field_simp [Real.pi_ne_zero]
    ring
  have hright : -(2 * a ^ 2 / (3 * Real.pi ^ 2)) +
      phi0 * a ^ 3 * (1 / 6 + 5 / (18 * Real.pi)) +
      (a ^ 4 / Real.pi ^ 2) * (7 / 12) +
      phi0 * a ^ 5 * (113 / 3840 + 1 / Real.pi ^ 4) +
      a ^ 8 * (128 + (1 / 240) * (1 / Real.pi ^ 2)) =
      (-(2 : ℝ) / (3 * Real.pi ^ 2) + phi0 * (1 / 6 + 5 / (18 * Real.pi)) * a +
        7 / (12 * Real.pi ^ 2) * a ^ 2 + phi0 * (113 / 3840 + 1 / Real.pi ^ 4) * a ^ 3 +
        (128 + 1 / (240 * Real.pi ^ 2)) * a ^ 6) * a ^ 2 := by ring
  have hsum' := add_le_add_left hsum (-(2 * a ^ 2 / (3 * Real.pi ^ 2)))
  have hsum'' : primaryValue a 0 ξ +
      (a ^ 2 / (3 * Real.pi ^ 2) + 5 * phi0 * a ^ 3 / (18 * Real.pi) +
        phi0 * a ^ 5 / Real.pi ^ 4) + 128 * a ^ 8 - targetLower a ξ ≤
      (-(2 : ℝ) / (3 * Real.pi ^ 2) + phi0 * (1 / 6 + 5 / (18 * Real.pi)) * a +
        7 / (12 * Real.pi ^ 2) * a ^ 2 + phi0 * (113 / 3840 + 1 / Real.pi ^ 4) * a ^ 3 +
        (128 + 1 / (240 * Real.pi ^ 2)) * a ^ 6) * a ^ 2 := by
    rw [hleft, ← hright]
    convert hsum' using 1 <;> ring
  linarith only [halias, hsum'', hn]

end KellerKlein.ZoneA
