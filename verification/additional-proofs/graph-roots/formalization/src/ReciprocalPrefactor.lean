import ReciprocalLog

noncomputable section
namespace SquareFlowerCompletion
namespace Reciprocal

def K (w : ℂ) : ℂ := (1 + (3 / 2 : ℂ) * w) / (P w * Q w)
def derivativeFactor (lam w v : ℂ) : ℂ := (lam + v)⁻¹ + (1 + v / lam) * K w

theorem K_sub_one {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    K w - 1 = -w * ((9 / 2 : ℂ) + 13 * w + 12 * w ^ 2 + 3 * w ^ 3) /
      (P w * Q w) := by
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have hp0 := Complex.slitPlane_ne_zero hp
  have hq0 := Complex.slitPlane_ne_zero hq
  dsimp [K]
  field_simp [hp0, hq0]
  dsimp [P, Q]
  ring

theorem norm_K_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    ‖K w - 1‖ ≤ 24 * ‖w‖ := by
  have hs : ‖w‖ ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by gcongr
  have hc : ‖w‖ ^ 3 ≤ (1 / 16 : ℝ) ^ 3 := by gcongr
  have hn : ‖(9 / 2 : ℂ) + 13 * w + 12 * w ^ 2 + 3 * w ^ 3‖ ≤ 6 := by
    have ht : ‖(9 / 2 : ℂ) + 13 * w + 12 * w ^ 2 + 3 * w ^ 3‖ ≤
        9 / 2 + 13 * ‖w‖ + 12 * ‖w‖ ^ 2 + 3 * ‖w‖ ^ 3 := by
      calc
        _ ≤ ‖(9 / 2 : ℂ) + 13 * w + 12 * w ^ 2‖ + ‖(3 : ℂ) * w ^ 3‖ := norm_add_le _ _
        _ ≤ (‖(9 / 2 : ℂ) + 13 * w‖ + ‖(12 : ℂ) * w ^ 2‖) + ‖(3 : ℂ) * w ^ 3‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖(9 / 2 : ℂ)‖ + ‖(13 : ℂ) * w‖) + ‖(12 : ℂ) * w ^ 2‖) + ‖(3 : ℂ) * w ^ 3‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by norm_num [norm_mul, norm_pow, norm_div]
    nlinarith
  obtain ⟨hp, hq⟩ := denominator_bounds hw
  have hpq : (1 / 4 : ℝ) ≤ ‖P w * Q w‖ := by rw [norm_mul]; nlinarith
  have hpos : 0 < ‖P w * Q w‖ := by linarith
  rw [K_sub_one hw, norm_div, norm_mul, norm_neg]
  apply (div_le_iff₀ hpos).2
  have hnum := mul_le_mul_of_nonneg_left hn (norm_nonneg w)
  have hden := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 24 * ‖w‖ by positivity)
  nlinarith

theorem norm_derivativeFactor_sub_one_le {lam w v : ℂ}
    (hw : ‖w‖ ≤ (1 / 16 : ℝ)) (hlam : ‖v‖ < ‖lam‖) :
    ‖derivativeFactor lam w v - 1‖ ≤
      1 / (‖lam‖ - ‖v‖) + 24 * ‖w‖ +
        (‖v‖ / ‖lam‖) * (1 + 24 * ‖w‖) := by
  have hk := norm_K_sub_one_le hw
  have hkbound : ‖K w‖ ≤ 1 + 24 * ‖w‖ := by
    have h := norm_add_le (K w - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hden : ‖lam‖ - ‖v‖ ≤ ‖lam + v‖ := by
    have h := norm_sub_norm_le lam (-v)
    simpa only [norm_neg, sub_neg_eq_add] using h
  have hinv : ‖(lam + v)⁻¹‖ ≤ 1 / (‖lam‖ - ‖v‖) := by
    rw [norm_inv, inv_eq_one_div]
    exact one_div_le_one_div_of_le (sub_pos.mpr hlam) hden
  calc
    ‖derivativeFactor lam w v - 1‖ = ‖((lam + v)⁻¹ + (K w - 1)) + (v / lam) * K w‖ := by
      congr 1; dsimp [derivativeFactor]; ring
    _ ≤ (‖(lam + v)⁻¹‖ + ‖K w - 1‖) + ‖(v / lam) * K w‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (1 / (‖lam‖ - ‖v‖) + 24 * ‖w‖) +
        (‖v‖ / ‖lam‖) * (1 + 24 * ‖w‖) := by
      rw [norm_mul, norm_div]
      gcongr
    _ = _ := by ring

#print axioms norm_K_sub_one_le
#print axioms norm_derivativeFactor_sub_one_le
end Reciprocal
end SquareFlowerCompletion
