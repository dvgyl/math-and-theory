import FourierModes

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000

noncomputable section

namespace AsymptoticCP

open FiniteCP
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem angle_pos (N : ℕ) : 0 < angle N := by
  unfold angle
  have hK : (0 : ℝ) < period N := by exact_mod_cast (NeZero.pos (period N))
  positivity

theorem period_mul_angle (N : ℕ) : (period N : ℝ) * angle N = Real.pi / 2 := by
  have hK : (period N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (period N))
  unfold angle
  field_simp
  ring

theorem mode1Angle_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 < mode1Angle N ∧ mode1Angle N < Real.pi := by
  have hK : (0 : ℝ) < period N := by exact_mod_cast (NeZero.pos (period N))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hperiod : (period N : ℝ) = 4 * (N : ℝ) + 3 := by simp [period]
  have h := period_mode1Angle N
  have hp : 0 < (N : ℝ) * (2 * Real.pi) := by positivity
  have hn : 0 < ((period N : ℝ) - 2 * N) * Real.pi := by
    apply mul_pos ?_ Real.pi_pos
    rw [hperiod]
    linarith
  constructor
  · apply (mul_lt_mul_left hK).mp
    simpa only [mul_zero, h] using hp
  · apply (mul_lt_mul_left hK).mp
    rw [h]
    nlinarith

theorem mode2Angle_bounds (N : ℕ) :
    0 < mode2Angle N ∧ mode2Angle N < Real.pi := by
  have hK : (0 : ℝ) < period N := by exact_mod_cast (NeZero.pos (period N))
  have hN' : (0 : ℝ) ≤ N := by positivity
  have hperiod : (period N : ℝ) = 4 * (N : ℝ) + 3 := by simp [period]
  have h := period_mode2Angle N
  push_cast at h
  have hp : 0 < ((N : ℝ) + 1) * (2 * Real.pi) := by positivity
  have hn : 0 < ((period N : ℝ) - 2 * (N + 1)) * Real.pi := by
    apply mul_pos ?_ Real.pi_pos
    rw [hperiod]
    linarith
  constructor
  · apply (mul_lt_mul_left hK).mp
    simpa only [mul_zero, h] using hp
  · apply (mul_lt_mul_left hK).mp
    rw [h]
    nlinarith

theorem spectralD1_pos (N : ℕ) (hN : 1 ≤ N) : 0 < spectralD1 N := by
  obtain ⟨h0, hp⟩ := mode1Angle_bounds N hN
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hp.le h0
  simp only [Real.cos_zero] at h
  unfold spectralD1
  linarith

theorem spectralD2_pos (N : ℕ) : 0 < spectralD2 N := by
  obtain ⟨h0, hp⟩ := mode2Angle_bounds N
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hp.le h0
  simp only [Real.cos_zero] at h
  unfold spectralD2
  linarith

theorem spectralD1_lt_D2 (N : ℕ) (hN : 1 ≤ N) : spectralD1 N < spectralD2 N := by
  obtain ⟨h0, hp⟩ := mode1Angle_bounds N hN
  have h12 : mode1Angle N < mode2Angle N := by
    unfold mode1Angle mode2Angle
    linarith [angle_pos N]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le (mode2Angle_bounds N).2.le h12
  unfold spectralD1 spectralD2
  linarith

theorem weight1_pos (N : ℕ) (κ : ℝ) (hN : 1 ≤ N) (hκ : spectralD2 N < κ) :
    0 < weight1 N κ := by
  have hk : 0 < κ := lt_trans (spectralD2_pos N) hκ
  have hd : 0 < κ - spectralD1 N := sub_pos.mpr (lt_trans (spectralD1_lt_D2 N hN) hκ)
  exact div_pos hk hd

theorem weight2_pos (N : ℕ) (κ : ℝ) (hκ : spectralD2 N < κ) :
    0 < weight2 N κ := by
  have hk : 0 < κ := lt_trans (spectralD2_pos N) hκ
  have hd : 0 < κ - spectralD2 N := sub_pos.mpr hκ
  exact div_pos (by positivity) hd

theorem sizeM_pos (N : ℕ) (κ : ℝ) (hN : 1 ≤ N) (hκ : spectralD2 N < κ) :
    0 < sizeM N κ := by
  unfold sizeM
  exact add_pos (mul_pos (spectralD1_pos N hN) (weight1_pos N κ hN hκ))
    (mul_pos (spectralD2_pos N) (weight2_pos N κ hκ))

def rawDual (N : ℕ) (κ r : ℝ) : E := rawPrimal N κ r - rawPrimal N κ (r + 1)

theorem rawDual_norm_sq (N : ℕ) (κ r : ℝ) (hN : 1 ≤ N) (hκ : spectralD2 N < κ) :
    ‖rawDual N κ r‖ ^ 2 = sizeM N κ := by
  unfold rawDual rawPrimal
  rw [wave_sub_norm_sq, Real.sq_sqrt (weight1_pos N κ hN hκ).le,
    Real.sq_sqrt (weight2_pos N κ hκ).le]
  have he : r + 1 - r = 1 := by ring
  simp only [he, one_mul, sizeM, spectralD1, spectralD2]

theorem dualPoints_norm_sq (N : ℕ) (κ : ℝ) (hN : 1 ≤ N) (hκ : spectralD2 N < κ)
    (i : Fin (period N)) : ‖dualPoints N κ i‖ ^ 2 = sizeM N κ := by
  rw [dualPoints_raw]
  exact rawDual_norm_sq N κ i.val hN hκ

def correlation (N : ℕ) (r : ℝ) : ℝ :=
  Real.cos (r * mode1Angle N) + 3 * Real.cos (r * mode2Angle N)

theorem wave_support_identity (a b φ ψ κ r δ : ℝ) :
    ⟪(wave a b φ ψ r - wave a b φ ψ (r + 1)) + κ • wave a b φ ψ (r + 1) -
        (wave a b φ ψ (r + 1) - wave a b φ ψ (r + 2)),
      (wave a b φ ψ (r + 1 + δ) - wave a b φ ψ (r + 1 + δ + 1)) -
        (wave a b φ ψ (r + 1) - wave a b φ ψ (r + 2))⟫ =
    (κ - (2 - 2 * Real.cos φ)) * a ^ 2 *
      (Real.cos (δ * φ) - Real.cos ((δ + 1) * φ) - 1 + Real.cos φ) +
    (κ - (2 - 2 * Real.cos ψ)) * b ^ 2 *
      (Real.cos (δ * ψ) - Real.cos ((δ + 1) * ψ) - 1 + Real.cos ψ) := by
  rw [wave_raw_normal]
  simp only [inner_sub_right, inner_wave]
  have h1 : r + 1 + δ - (r + 1) = δ := by ring
  have h2 : r + 1 + δ + 1 - (r + 1) = δ + 1 := by ring
  have h3 : r + 2 - (r + 1) = 1 := by ring
  simp only [h1, h2, h3, sub_self, zero_mul, one_mul, Real.cos_zero]
  ring

theorem rawDual_support_identity (N : ℕ) (κ r δ : ℝ)
    (hN : 1 ≤ N) (hκ : spectralD2 N < κ) :
    ⟪rawDual N κ r + κ • rawPrimal N κ (r + 1) - rawDual N κ (r + 1),
      rawDual N κ (r + 1 + δ) - rawDual N κ (r + 1)⟫ =
      -κ * (4 - correlation N 1 - correlation N δ + correlation N (δ + 1)) := by
  have hw1 : (κ - spectralD1 N) * (Real.sqrt (weight1 N κ)) ^ 2 = κ := by
    rw [Real.sq_sqrt (weight1_pos N κ hN hκ).le]
    unfold weight1
    field_simp [ne_of_gt (sub_pos.mpr (lt_trans (spectralD1_lt_D2 N hN) hκ))]
  have hw2 : (κ - spectralD2 N) * (Real.sqrt (weight2 N κ)) ^ 2 = 3 * κ := by
    rw [Real.sq_sqrt (weight2_pos N κ hκ).le]
    unfold weight2
    field_simp [ne_of_gt (sub_pos.mpr hκ)]
  unfold rawDual rawPrimal
  have hr : r + 1 + 1 = r + 2 := by ring
  rw [hr, wave_support_identity]
  change (κ - spectralD1 N) * (Real.sqrt (weight1 N κ)) ^ 2 * _ +
    (κ - spectralD2 N) * (Real.sqrt (weight2 N κ)) ^ 2 * _ = _
  rw [hw1, hw2]
  simp only [correlation, one_mul]
  ring

end AsymptoticCP
