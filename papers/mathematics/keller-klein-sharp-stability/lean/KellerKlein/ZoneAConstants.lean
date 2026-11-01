import KellerKlein.ZoneAKernel
import KellerKlein.GaussianMoments

noncomputable section

namespace KellerKlein.ZoneA

lemma phi0_lower : (39 : ℝ) / 100 ≤ phi0 := by
  have hid := two_pi_phi0_sq
  have hp := Real.pi_lt_d2
  have hnonneg := mul_nonneg (show 0 ≤ 3.15 - Real.pi by linarith) (sq_nonneg phi0)
  by_contra h
  have hφ : phi0 < 39 / 100 := lt_of_not_ge h
  have hprod : 0 ≤ (39 / 100 - phi0) * (39 / 100 + phi0) := by
    exact mul_nonneg (by linarith) (by linarith [phi0_pos])
  nlinarith

lemma phi0_upper : phi0 ≤ (2 : ℝ) / 5 := by
  have hid := two_pi_phi0_sq
  have hp := Real.pi_gt_d2
  have hnonneg := mul_nonneg (show 0 ≤ Real.pi - 3.14 by linarith) (sq_nonneg phi0)
  by_contra h
  have hφ : 2 / 5 < phi0 := lt_of_not_ge h
  have hprod : 0 < (phi0 - 2 / 5) * (phi0 + 2 / 5) := by
    exact mul_pos (by linarith) (by linarith [phi0_pos])
  nlinarith

lemma pi_sq_lower : (9 : ℝ) ≤ Real.pi ^ 2 := by
  have hp := Real.pi_gt_d2
  nlinarith [sq_nonneg (Real.pi - 3)]

lemma pi_sq_upper : Real.pi ^ 2 ≤ (10 : ℝ) := by
  have hp := Real.pi_lt_d2
  have hprod : 0 ≤ (3.15 - Real.pi) * (3.15 + Real.pi) :=
    mul_nonneg (by linarith) (by linarith [Real.pi_pos])
  nlinarith

lemma A_bound {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) : A ξ ≤ 5 / 16 := by
  have h2 := pow_le_pow_left₀ hξ hξ1 2
  have h3 := pow_le_pow_left₀ hξ hξ1 3
  norm_num at h2 h3
  unfold A
  nlinarith

lemma AL_bound {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) : AL ξ ≤ 19 / 48 := by
  have h2 := pow_le_pow_left₀ hξ hξ1 2
  have h3 := pow_le_pow_left₀ hξ hξ1 3
  norm_num at h2 h3
  unfold AL
  nlinarith

lemma C_bound {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) : C ξ ≤ 113 / 11520 := by
  have h3 := pow_le_pow_left₀ hξ hξ1 3
  have h4 := pow_le_pow_left₀ hξ hξ1 4
  have h5 := pow_le_pow_left₀ hξ hξ1 5
  norm_num at h3 h4 h5
  unfold C
  nlinarith

lemma high_theta_cubic_bound {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    (1 : ℝ) / 6 + ξ ^ 2 / 2 - (361 / 400 : ℝ) * (1 + ξ) / 4 ≤ -449 / 9600 := by
  have hprod : 0 ≤ ξ * (1 / 2 - ξ) := mul_nonneg hξ (by linarith)
  nlinarith

lemma high_theta_numerical_margin {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 7 / 100) :
    -(449 / 9600 : ℝ) * phi0 + 5 / (4 * Real.pi ^ 2) * a +
      phi0 * (1371 / 1280 + 3 / Real.pi ^ 4) * a ^ 2 +
      (128 + 1 / (240 * Real.pi ^ 2)) * a ^ 5 ≤ -1 / 200 := by
  have hp2 : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hp4 : 0 < Real.pi ^ 4 := pow_pos Real.pi_pos 4
  have h4lower : (81 : ℝ) ≤ Real.pi ^ 4 := by nlinarith [pi_sq_lower, sq_nonneg (Real.pi^2 - 9)]
  have hc4 : 5 / (4 * Real.pi ^ 2) ≤ (5 : ℝ) / 36 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi ^ 2)).2
    nlinarith [pi_sq_lower]
  have hrec4 : 3 / Real.pi ^ 4 ≤ (1 : ℝ) / 27 := by
    apply (div_le_iff₀ hp4).2
    nlinarith
  have hc5 : phi0 * (1371 / 1280 + 3 / Real.pi ^ 4) ≤
      (2 / 5 : ℝ) * (1371 / 1280 + 1 / 27) := by
    exact mul_le_mul phi0_upper (by linarith) (by positivity) (by norm_num)
  have hc8 : 128 + 1 / (240 * Real.pi ^ 2) ≤ (128 : ℝ) + 1 / 2160 := by
    have h : 1 / (240 * Real.pi ^ 2) ≤ (1 : ℝ) / 2160 := by
      apply (div_le_iff₀ (by positivity : 0 < 240 * Real.pi ^ 2)).2
      nlinarith [pi_sq_lower]
    linarith
  have ht4 := mul_le_mul hc4 ha1 ha (by norm_num : 0 ≤ (5 : ℝ) / 36)
  have ha2 := pow_le_pow_left₀ ha ha1 2
  have ha5 := pow_le_pow_left₀ ha ha1 5
  have ht5 := mul_le_mul hc5 ha2 (sq_nonneg a) (by norm_num :
      0 ≤ (2 / 5 : ℝ) * (1371 / 1280 + 1 / 27))
  have ht8 := mul_le_mul hc8 ha5 (pow_nonneg ha 5) (by norm_num :
      0 ≤ (128 : ℝ) + 1 / 2160)
  have ht0 := mul_le_mul_of_nonpos_left phi0_lower
      (by norm_num : -(449 / 9600 : ℝ) ≤ 0)
  norm_num at ht0 ht4 ht5 ht8 ⊢
  linarith only [ht0, ht4, ht5, ht8]

lemma low_theta_numerical_margin {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 7 / 100) :
    -(2 : ℝ) / (3 * Real.pi ^ 2) +
      phi0 * (1 / 6 + 5 / (18 * Real.pi)) * a +
      7 / (12 * Real.pi ^ 2) * a ^ 2 +
      phi0 * (113 / 3840 + 1 / Real.pi ^ 4) * a ^ 3 +
      (128 + 1 / (240 * Real.pi ^ 2)) * a ^ 6 ≤ -1 / 20 := by
  have hp2 : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hp4 : 0 < Real.pi ^ 4 := pow_pos Real.pi_pos 4
  have hp3 : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have h4lower : (81 : ℝ) ≤ Real.pi ^ 4 := by
    nlinarith [pi_sq_lower, sq_nonneg (Real.pi ^ 2 - 9)]
  have hc0 : -(2 : ℝ) / (3 * Real.pi ^ 2) ≤ -1 / 15 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)).2
    nlinarith [pi_sq_upper]
  have hrec1 : 5 / (18 * Real.pi) ≤ (5 : ℝ) / 54 := by
    apply (div_le_iff₀ (by positivity : 0 < 18 * Real.pi)).2
    nlinarith
  have hc1 : phi0 * (1 / 6 + 5 / (18 * Real.pi)) ≤
      (2 / 5 : ℝ) * (1 / 6 + 5 / 54) := by
    exact mul_le_mul phi0_upper (by linarith) (by positivity) (by norm_num)
  have hc2 : 7 / (12 * Real.pi ^ 2) ≤ (7 : ℝ) / 108 := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * Real.pi ^ 2)).2
    nlinarith [pi_sq_lower]
  have hrec4 : 1 / Real.pi ^ 4 ≤ (1 : ℝ) / 81 := by
    apply (div_le_iff₀ hp4).2
    nlinarith
  have hc3 : phi0 * (113 / 3840 + 1 / Real.pi ^ 4) ≤
      (2 / 5 : ℝ) * (113 / 3840 + 1 / 81) := by
    exact mul_le_mul phi0_upper (by linarith) (by positivity) (by norm_num)
  have hc6 : 128 + 1 / (240 * Real.pi ^ 2) ≤ (128 : ℝ) + 1 / 2160 := by
    have h : 1 / (240 * Real.pi ^ 2) ≤ (1 : ℝ) / 2160 := by
      apply (div_le_iff₀ (by positivity : 0 < 240 * Real.pi ^ 2)).2
      nlinarith [pi_sq_lower]
    linarith
  have ht1 := mul_le_mul hc1 ha1 ha (by norm_num :
      0 ≤ (2 / 5 : ℝ) * (1 / 6 + 5 / 54))
  have ht2 := mul_le_mul hc2 (pow_le_pow_left₀ ha ha1 2) (sq_nonneg a)
    (by norm_num : 0 ≤ (7 : ℝ) / 108)
  have ht3 := mul_le_mul hc3 (pow_le_pow_left₀ ha ha1 3) (pow_nonneg ha 3)
    (by norm_num : 0 ≤ (2 / 5 : ℝ) * (113 / 3840 + 1 / 81))
  have ht6 := mul_le_mul hc6 (pow_le_pow_left₀ ha ha1 6) (pow_nonneg ha 6)
    (by norm_num : 0 ≤ (128 : ℝ) + 1 / 2160)
  norm_num at hc0 ht1 ht2 ht3 ht6 ⊢
  linarith only [hc0, ht1, ht2, ht3, ht6]

end KellerKlein.ZoneA
