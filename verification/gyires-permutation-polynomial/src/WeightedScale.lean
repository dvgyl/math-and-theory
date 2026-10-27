module

public import TwentyThreeTail

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound

open Matrix

theorem transfer_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (hn : 4 ≤ n) :
    2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤
      prefactor n * (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hbLac⟩ := weightScale_properties ha hb hc
  rcases eq_or_lt_of_le hL0 with hL | hL
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    subst a; subst b; subst c
    have h1 : transferOne 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferOne]
    have h2 : transferTwo 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferTwo]
    cases n <;> norm_num [weightScale, positiveRoot, h1, h2, Matrix.trace_one, prefactor, K]
  · let L := weightScale a b c
    have hLne : L ≠ 0 := ne_of_gt hL
    have han : 0 ≤ a/L := div_nonneg ha hL0
    have hbn : 0 ≤ b/L := div_nonneg hb hL0
    have hcn : 0 ≤ c/L := div_nonneg hc hL0
    have han1 : a/L ≤ 1 := (div_le_one hL).2 haL
    have hcn1 : c/L ≤ 1 := (div_le_one hL).2 hcL
    have hbac : b/L + (a/L)*(c/L) ≤ 1 := by
      have heq : b/L + (a/L)*(c/L) = (b*L+a*c)/L^2 := by field_simp
      rw [heq, div_le_one (sq_pos_of_pos hL)]
      exact hbLac
    have hnorm := normalized_trace_bound han hbn hcn han1 hcn1 hbac n hn
    change _ ≤ prefactor n at hnorm
    have hd : a^2+b^2+c^2 = L^2*((a/L)^2+(b/L)^2+(c/L)^2) := by field_simp
    have he : b*(a+c) = L^2*((b/L)*(a/L+c/L)) := by field_simp
    have hf : a*c = L^2*((a/L)*(c/L)) := by field_simp
    rw [hd, he, hf, transferOne_scale, transferTwo_scale, smul_pow, smul_pow,
      Matrix.trace_smul, Matrix.trace_smul, mul_pow]
    simp only [smul_eq_mul]
    have hscaled := mul_le_mul_of_nonneg_right hnorm (pow_nonneg (sq_nonneg L) n)
    have hpow : (L^2)^n = L^(2*n) := (pow_mul L 2 n).symm
    change _ ≤ prefactor n * L^(2*n)
    rw [hpow] at hscaled ⊢
    nlinarith

theorem transfer_tail_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (hn : 23 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) ≤
      (weightScale a b c)^(2*n) := by
  have hscale := (weightScale_properties ha hb hc).1
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n (by omega))
    (dimensionConstant_nonneg n)
  have htail := mul_le_mul_of_nonneg_right (le_of_lt (rational_tail n hn))
    (pow_nonneg hscale (2*n))
  nlinarith

theorem transfer_tail_bound_strict {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) (n : ℕ) (hn : 23 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) <
      (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hrest⟩ := weightScale_properties ha hb hc
  have hL : 0 < weightScale a b c := by
    rcases hpositive with h | h | h <;> linarith
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n (by omega))
    (dimensionConstant_nonneg n)
  have htail := mul_lt_mul_of_pos_right (rational_tail n hn) (pow_pos hL (2*n))
  nlinarith

end MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound
