import KellerKlein.Envelopes
import Mathlib.Data.Complex.ExponentialBounds

namespace KellerKlein

lemma exp_neg_three_halves_gt_fifth : (1 / 5 : ℝ) < Real.exp (-(3 / 2 : ℝ)) := by
  have hehalf := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hehalf
  have heone : Real.exp 1 ≤ (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he : Real.exp (3 / 2 : ℝ) < 5 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
    calc
      Real.exp 1 * Real.exp (1 / 2) ≤ (68 / 25 : ℝ) * (27 / 16 : ℝ) :=
        mul_le_mul heone hehalf (Real.exp_pos _).le (by norm_num)
      _ < 5 := by norm_num
  rw [Real.exp_neg]
  simpa only [one_div] using
    (inv_lt_inv₀ (by norm_num : 0 < (5 : ℝ)) (Real.exp_pos _)).mpr he

lemma exp_neg_eightyone_fiftieth_lt_fifth :
    Real.exp (-(81 / 50 : ℝ)) < (1 / 5 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (81 / 50 : ℝ)) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hh : (5 : ℝ) < Real.exp (81 / 50 : ℝ) := by linarith
  rw [Real.exp_neg]
  simpa only [one_div] using
    (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : 0 < (5 : ℝ))).mpr hh

lemma cos_seventeen_tenths_gt_neg_fifth :
    -(1 / 5 : ℝ) < Real.cos (17 / 10 : ℝ) := by
  have hh := cos_lower_sextic (by norm_num : 0 ≤ (17 / 10 : ℝ))
  norm_num at hh
  linarith

lemma cos_nine_fifths_lt_neg_fifth :
    Real.cos (9 / 5 : ℝ) < -(1 / 5 : ℝ) := by
  let δ : ℝ := 9 / 5 - Real.pi / 2
  have hδlo : (8 / 35 : ℝ) ≤ δ := by dsimp [δ]; linarith [Real.pi_lt_d4]
  have hδhi : δ ≤ (3 / 10 : ℝ) := by dsimp [δ]; linarith [Real.pi_gt_three]
  have hδ0 : 0 ≤ δ := le_trans (by norm_num : (0 : ℝ) ≤ 8 / 35) hδlo
  have hpow : δ ^ 3 ≤ (3 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hδ0 hδhi 3
  have hs : (1 / 5 : ℝ) < Real.sin δ := by
    have hh := sin_lower_cubic hδ0
    nlinarith
  have hcos : Real.cos (9 / 5 : ℝ) = -Real.sin δ := by
    conv_lhs => rw [show (9 / 5 : ℝ) = Real.pi / 2 + δ by dsimp [δ]; ring]
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [hcos]
  linarith

/-- Rational localization of the crossover used in the integral estimates. -/
theorem crossoverRoot_bounds : (17 / 10 : ℝ) < crossoverRoot ∧
    crossoverRoot < (9 / 5 : ℝ) := by
  have hpos : 0 < crossoverRoot := by linarith [crossoverRoot_spec.1, Real.pi_pos]
  have hcneg : Real.cos crossoverRoot < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
    crossoverRoot_spec.1 (by linarith [crossoverRoot_spec.2.1, Real.pi_pos])
  have hr := crossoverRoot_spec.2.2
  rw [abs_of_neg hcneg] at hr
  constructor
  · by_contra hn
    have hle : crossoverRoot ≤ (17 / 10 : ℝ) := le_of_not_gt hn
    have hc : Real.cos (17 / 10 : ℝ) ≤ Real.cos crossoverRoot :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨hpos.le, crossoverRoot_spec.2.1.le⟩
        ⟨by norm_num, by linarith [Real.pi_gt_three]⟩ hle
    have he : Real.exp (-(3 / 2 : ℝ)) ≤ Real.exp (-(crossoverRoot ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      have hsq : crossoverRoot ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      nlinarith
    linarith [cos_seventeen_tenths_gt_neg_fifth, exp_neg_three_halves_gt_fifth]
  · by_contra hn
    have hle : (9 / 5 : ℝ) ≤ crossoverRoot := le_of_not_gt hn
    have hc : Real.cos crossoverRoot ≤ Real.cos (9 / 5 : ℝ) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
        ⟨hpos.le, crossoverRoot_spec.2.1.le⟩ hle
    have he : Real.exp (-(crossoverRoot ^ 2) / 2) ≤ Real.exp (-(81 / 50 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hsq : (9 / 5 : ℝ) ^ 2 ≤ crossoverRoot ^ 2 := pow_le_pow_left₀ (by norm_num) hle 2
      nlinarith
    linarith [cos_nine_fifths_lt_neg_fifth, exp_neg_eightyone_fiftieth_lt_fifth]

end KellerKlein
