module

public import SharpTransfer

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp

open Matrix

lemma rational_growth_lower (n : ℕ) (hn : 48 ≤ n) :
    (169 / 70 : ℝ) * (n:ℝ)^n < ((n:ℝ)+1)^n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn48 : (48:ℝ) ≤ n := by exact_mod_cast hn
  have hbase := cubic_binomial_lower (1/(n:ℝ)) (by positivity) n
  have hpoly : (169/70:ℝ) < 1 + n*(1/(n:ℝ)) +
      (n:ℝ)*((n:ℝ)-1)/2*(1/(n:ℝ))^2 +
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)/6*(1/(n:ℝ))^3 := by
    field_simp
    nlinarith [sq_nonneg ((n:ℝ)-48)]
  have hbound := lt_of_lt_of_le hpoly hbase
  have hpow : (1+1/(n:ℝ))^n * (n:ℝ)^n = ((n:ℝ)+1)^n := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hmul := mul_lt_mul_of_pos_right hbound (pow_pos hn0 n)
  rwa [hpow] at hmul

lemma rational_tail_integer (n : ℕ) (hn : 48 ≤ n) :
    16 * (n.factorial:ℝ) * (169/70:ℝ)^n < (n:ℝ)^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnp : (0:ℝ) < (n:ℝ)+1 := by positivity
      have hgrowth := rational_growth_lower n hn
      have hleft := mul_lt_mul_of_pos_right ih (by norm_num : (0:ℝ) < 169/70)
      have hcombined := lt_trans hleft (show (n:ℝ)^n * (169/70:ℝ) < ((n:ℝ)+1)^n by
        simpa [mul_comm] using hgrowth)
      have hfinal := mul_lt_mul_of_pos_left hcombined hnp
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, pow_succ]
      nlinarith

theorem rational_tail (n : ℕ) (hn : 48 ≤ n) :
    16 * dimensionConstant n * (169/70:ℝ)^n < 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) < (n:ℝ)^n := pow_pos hn0 n
  have h := rational_tail_integer n hn
  unfold dimensionConstant
  apply (mul_lt_mul_iff_right₀ hp).mp
  field_simp
  exact h



theorem transfer_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤
      16 * (169 / 70 : ℝ)^n * (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hbLac⟩ := weightScale_properties ha hb hc
  rcases eq_or_lt_of_le hL0 with hL | hL
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    subst a; subst b; subst c
    have h1 : transferOne 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferOne]
    have h2 : transferTwo 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferTwo]
    cases n <;> norm_num [weightScale, positiveRoot, h1, h2, Matrix.trace_one]
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
    have hnorm := normalized_trace_bound han hbn hcn han1 hcn1 hbac n
    change _ ≤ 16 * (169/70:ℝ)^n at hnorm
    have hd : a^2+b^2+c^2 = L^2*((a/L)^2+(b/L)^2+(c/L)^2) := by field_simp
    have he : b*(a+c) = L^2*((b/L)*(a/L+c/L)) := by field_simp
    have hf : a*c = L^2*((a/L)*(c/L)) := by field_simp
    rw [hd, he, hf, transferOne_scale, transferTwo_scale, smul_pow, smul_pow,
      Matrix.trace_smul, Matrix.trace_smul, mul_pow]
    simp only [smul_eq_mul]
    have hscaled := mul_le_mul_of_nonneg_right hnorm (pow_nonneg (sq_nonneg L) n)
    have hpow : (L^2)^n = L^(2*n) := (pow_mul L 2 n).symm
    change _ ≤ 16 * (169/70:ℝ)^n * L^(2*n)
    rw [hpow] at hscaled ⊢
    nlinarith

theorem transfer_tail_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (hn : 48 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) ≤
      (weightScale a b c)^(2*n) := by
  have hscale := (weightScale_properties ha hb hc).1
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n)
    (dimensionConstant_nonneg n)
  have htail := mul_le_mul_of_nonneg_right (le_of_lt (rational_tail n hn))
    (pow_nonneg hscale (2*n))
  nlinarith

theorem transfer_tail_bound_strict {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) (n : ℕ) (hn : 48 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) <
      (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hrest⟩ := weightScale_properties ha hb hc
  have hL : 0 < weightScale a b c := by
    rcases hpositive with h | h | h <;> linarith
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n)
    (dimensionConstant_nonneg n)
  have htail := mul_lt_mul_of_pos_right (rational_tail n hn) (pow_pos hL (2*n))
  nlinarith

end MathAndTheory.Gyires.PermutationTransfer.Sharp
