import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import TrigSupport

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace TrigGrid

open Real

def fourierA (t : ℝ) (j : ℕ) : ℝ :=
  cos ((j : ℝ) * (π / 2 - 3 * t)) + 3 * cos ((j : ℝ) * (π / 2 + t))

theorem trig_triple_identity (a u : ℝ) :
    cos (a - 3 * u) + 3 * cos (a + u) =
      4 * cos a * cos u ^ 3 - 4 * sin a * sin u ^ 3 := by
  rw [cos_sub, cos_add, cos_three_mul, sin_three_mul]
  ring

theorem fourierA_cubic (t : ℝ) (j : ℕ) :
    fourierA t j = 4 * cos ((j : ℝ) * π / 2) * cos ((j : ℝ) * t) ^ 3 -
      4 * sin ((j : ℝ) * π / 2) * sin ((j : ℝ) * t) ^ 3 := by
  unfold fourierA
  rw [show (j : ℝ) * (π / 2 - 3 * t) = (j : ℝ) * π / 2 - 3 * ((j : ℝ) * t) by ring,
      show (j : ℝ) * (π / 2 + t) = (j : ℝ) * π / 2 + (j : ℝ) * t by ring]
  exact trig_triple_identity _ _

theorem quarter_cos (q r : ℕ) :
    cos (((4 * q + r : ℕ) : ℝ) * π / 2) = cos ((r : ℝ) * π / 2) := by
  rw [show (((4 * q + r : ℕ) : ℝ) * π / 2) =
    (r : ℝ) * π / 2 + (q : ℝ) * (2 * π) by push_cast; ring]
  exact cos_add_nat_mul_two_pi _ q

theorem quarter_sin (q r : ℕ) :
    sin (((4 * q + r : ℕ) : ℝ) * π / 2) = sin ((r : ℝ) * π / 2) := by
  rw [show (((4 * q + r : ℕ) : ℝ) * π / 2) =
    (r : ℝ) * π / 2 + (q : ℝ) * (2 * π) by push_cast; ring]
  exact sin_add_nat_mul_two_pi _ q

theorem fourierA_mod_zero (t : ℝ) (j : ℕ) (hj : j % 4 = 0) :
    fourierA t j = 4 * cos ((j : ℝ) * t) ^ 3 := by
  have he : j = 4 * (j / 4) + 0 := by omega
  rw [fourierA_cubic]
  have hc : cos ((j : ℝ) * π / 2) = 1 := by
    rw [he, quarter_cos]
    norm_num
  have hs : sin ((j : ℝ) * π / 2) = 0 := by
    rw [he, quarter_sin]
    norm_num
  rw [hc, hs]
  ring

theorem fourierA_mod_one (t : ℝ) (j : ℕ) (hj : j % 4 = 1) :
    fourierA t j = -4 * sin ((j : ℝ) * t) ^ 3 := by
  have he : j = 4 * (j / 4) + 1 := by omega
  rw [fourierA_cubic]
  have hc : cos ((j : ℝ) * π / 2) = 0 := by
    rw [he, quarter_cos]
    norm_num
  have hs : sin ((j : ℝ) * π / 2) = 1 := by
    rw [he, quarter_sin]
    norm_num
  rw [hc, hs]
  ring

theorem fourierA_mod_two (t : ℝ) (j : ℕ) (hj : j % 4 = 2) :
    fourierA t j = -4 * cos ((j : ℝ) * t) ^ 3 := by
  have he : j = 4 * (j / 4) + 2 := by omega
  rw [fourierA_cubic]
  have hc : cos ((j : ℝ) * π / 2) = -1 := by
    rw [he, quarter_cos]
    norm_num
  have hs : sin ((j : ℝ) * π / 2) = 0 := by
    rw [he, quarter_sin]
    norm_num
  rw [hc, hs]
  ring

theorem fourierA_mod_three (t : ℝ) (j : ℕ) (hj : j % 4 = 3) :
    fourierA t j = 4 * sin ((j : ℝ) * t) ^ 3 := by
  have he : j = 4 * (j / 4) + 3 := by omega
  have hangle : (3 : ℝ) * π / 2 = π + π / 2 := by ring
  rw [fourierA_cubic]
  have hc : cos ((j : ℝ) * π / 2) = 0 := by
    rw [he, quarter_cos]
    norm_num only [Nat.cast_ofNat]
    rw [hangle, cos_add]
    norm_num
  have hs : sin ((j : ℝ) * π / 2) = -1 := by
    rw [he, quarter_sin]
    norm_num only [Nat.cast_ofNat]
    rw [hangle, sin_add]
    norm_num
  rw [hc, hs]
  ring

theorem sin_five_mul (t : ℝ) :
    sin (5 * t) = 16 * sin t ^ 5 - 20 * sin t ^ 3 + 5 * sin t := by
  rw [show 5 * t = 2 * t + 3 * t by ring, sin_add,
    sin_two_mul, cos_three_mul, cos_two_mul, sin_three_mul]
  linear_combination 8 * sin t * (cos t ^ 2 - 2 * sin t ^ 2 + 1) *
    (sin_sq_add_cos_sq t)

theorem four_sin_le_sin_five {t : ℝ} (hs : 0 ≤ sin t) (hsmall : sin t ≤ 1 / 8) :
    4 * sin t ≤ sin (5 * t) := by
  rw [sin_five_mul]
  have hsq : sin t ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hsmall)]
  have hf : 0 ≤ 1 - 20 * sin t ^ 2 + 16 * sin t ^ 4 := by
    nlinarith [sq_nonneg (sin t ^ 2)]
  have hm := mul_nonneg hs hf
  nlinarith

theorem sin_ge_of_interval {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvu : v ≤ π - u) :
    sin u ≤ sin v := by
  by_cases hv : v ≤ π / 2
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hv huv
  · have h := sin_le_sin_of_le_of_le_pi_div_two
      (show -(π / 2) ≤ u by linarith [pi_pos])
      (show π - v ≤ π / 2 by linarith) (show u ≤ π - v by linarith)
    simpa only [sin_pi_sub] using h

theorem grid_sin_lower {K j : ℕ} {t : ℝ}
    (hK : K % 4 = 3) (hj : j % 4 = 0) (hjlo : 1 ≤ j) (hjhi : j < K)
    (ht : 0 < t) (hKt : (K : ℝ) * t = π / 2) (hs : sin t ≤ 1 / 8) :
    4 * sin t ≤ sin (2 * ((j : ℝ) * t) + t) := by
  have hj4 : 4 ≤ j := by omega
  have hjK : j + 3 ≤ K := by omega
  have hj4r : (4 : ℝ) ≤ j := by exact_mod_cast hj4
  have hjKr : (j : ℝ) + 3 ≤ K := by exact_mod_cast hjK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have htpi : t ≤ π / 2 := by nlinarith
  have hsin : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [pi_pos])
  apply (four_sin_le_sin_five hsin hs).trans
  apply sin_ge_of_interval (by positivity)
  · nlinarith
  · nlinarith

theorem fourier_support_of_cubic_bound {K j : ℕ} {t : ℝ}
    (hK : K % 4 = 3) (hjlo : 1 ≤ j) (hjhi : j < K)
    (ht : 0 < t) (hKt : (K : ℝ) * t = π / 2) (hs : sin t ≤ 1 / 8)
    (hcubic : ∀ a : ℝ, 0 ≤ a → a + t ≤ π / 2 →
      4 * sin t ≤ sin (2 * a + t) → cos a ^ 3 + sin (a + t) ^ 3 ≤ 1) :
    4 * sin t ^ 3 ≤ fourierA t 0 - fourierA t 1 - fourierA t j + fourierA t (j + 1) := by
  have hA0 : fourierA t 0 = 4 := by norm_num [fourierA]
  have hA1 : fourierA t 1 = -4 * sin t ^ 3 := by
    simpa using fourierA_mod_one t 1 (by norm_num)
  rw [hA0, hA1]
  suffices hd : fourierA t j - fourierA t (j + 1) ≤ 4 by linarith
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjKr : (j : ℝ) + 1 ≤ K := by exact_mod_cast (show j + 1 ≤ K by omega)
  have hat : (j : ℝ) * t + t ≤ π / 2 := by nlinarith
  have ha : 0 ≤ (j : ℝ) * t := mul_nonneg hjr ht.le
  have he : ((j + 1 : ℕ) : ℝ) * t = (j : ℝ) * t + t := by push_cast; ring
  have hsina : 0 ≤ sin ((j : ℝ) * t) :=
    sin_nonneg_of_nonneg_of_le_pi ha (by linarith [pi_pos])
  have hsinb : 0 ≤ sin (((j + 1 : ℕ) : ℝ) * t) := by
    rw [he]
    exact sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos])
  have hcosa : 0 ≤ cos ((j : ℝ) * t) :=
    cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) (by linarith)
  have hcosb : 0 ≤ cos (((j + 1 : ℕ) : ℝ) * t) := by
    rw [he]
    exact cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) hat
  have hcosa3 : 0 ≤ cos ((j : ℝ) * t) ^ 3 := pow_nonneg hcosa _
  have hcosb3 : 0 ≤ cos (((j + 1 : ℕ) : ℝ) * t) ^ 3 := pow_nonneg hcosb _
  have hsina3 : 0 ≤ sin ((j : ℝ) * t) ^ 3 := pow_nonneg hsina _
  have hsinb3 : 0 ≤ sin (((j + 1 : ℕ) : ℝ) * t) ^ 3 := pow_nonneg hsinb _
  have hcosb1 : cos (((j + 1 : ℕ) : ℝ) * t) ^ 3 ≤ 1 := pow_le_one₀ hcosb (cos_le_one _)
  have hsina1 : sin ((j : ℝ) * t) ^ 3 ≤ 1 := pow_le_one₀ hsina (sin_le_one _)
  have hjmod : j % 4 < 4 := Nat.mod_lt j (by decide)
  interval_cases hm : j % 4
  · rw [fourierA_mod_zero t j hm, fourierA_mod_one t (j + 1) (by omega), he]
    have hg := hcubic ((j : ℝ) * t) ha hat
      (grid_sin_lower hK hm hjlo hjhi ht hKt hs)
    linarith
  · rw [fourierA_mod_one t j hm, fourierA_mod_two t (j + 1) (by omega)]
    linarith
  · rw [fourierA_mod_two t j hm, fourierA_mod_three t (j + 1) (by omega)]
    linarith
  · rw [fourierA_mod_three t j hm, fourierA_mod_zero t (j + 1) (by omega)]
    linarith

/-- Uniform strict supporting gap for the actual finite Fourier grid. -/
theorem fourier_support {K j : ℕ} {t : ℝ}
    (hK : K % 4 = 3) (hjlo : 1 ≤ j) (hjhi : j < K)
    (ht : 0 < t) (hKt : (K : ℝ) * t = π / 2) (hs : sin t ≤ 1 / 8) :
    4 * sin t ^ 3 ≤ fourierA t 0 - fourierA t 1 - fourierA t j + fourierA t (j + 1) := by
  apply fourier_support_of_cubic_bound hK hjlo hjhi ht hKt hs
  intro a ha hat hr
  exact TrigSupport.cos_cube_add_sin_cube_le_one ht hs ha hat hr

end TrigGrid

#print axioms TrigGrid.fourier_support
