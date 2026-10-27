module

public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import MathAndTheory.Mathematics.Gyires.PermutationTransfer
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer

open Matrix

lemma cubic_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    1 + n*x + (n:ℝ)*((n:ℝ)-1)/2*x^2 +
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)/6*x^3 ≤ (1+x)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hstep := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+x)
      have hfactor : 0 ≤ (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2) := by
        rcases n with _ | n
        · norm_num
        rcases n with _ | n
        · norm_num
        push_cast
        ring_nf
        positivity
      have hquartic := mul_nonneg hfactor (pow_nonneg hx 4)
      rw [pow_succ (1+x)]
      push_cast
      nlinarith

lemma rational_growth_lower (n : ℕ) (hn : 94 ≤ n) :
    (51 / 20 : ℝ) * (n:ℝ)^n < ((n:ℝ)+1)^n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn94 : (94:ℝ) ≤ n := by exact_mod_cast hn
  have hbase := cubic_binomial_lower (1/(n:ℝ)) (by positivity) n
  have hpoly : (51/20:ℝ) < 1 + n*(1/(n:ℝ)) +
      (n:ℝ)*((n:ℝ)-1)/2*(1/(n:ℝ))^2 +
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)/6*(1/(n:ℝ))^3 := by
    field_simp
    nlinarith [sq_nonneg ((n:ℝ)-94)]
  have hbound := lt_of_lt_of_le hpoly hbase
  have hpow : (1+1/(n:ℝ))^n * (n:ℝ)^n = ((n:ℝ)+1)^n := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hmul := mul_lt_mul_of_pos_right hbound (pow_pos hn0 n)
  rwa [hpow] at hmul

lemma rational_tail_integer (n : ℕ) (hn : 94 ≤ n) :
    16 * (n.factorial:ℝ) * (51/20:ℝ)^n < (n:ℝ)^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnp : (0:ℝ) < (n:ℝ)+1 := by positivity
      have hgrowth := rational_growth_lower n hn
      have hleft := mul_lt_mul_of_pos_right ih (by norm_num : (0:ℝ) < 51/20)
      have hcombined := lt_trans hleft (show (n:ℝ)^n * (51/20:ℝ) < ((n:ℝ)+1)^n by
        simpa [mul_comm] using hgrowth)
      have hfinal := mul_lt_mul_of_pos_left hcombined hnp
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, pow_succ]
      nlinarith

theorem rational_tail (n : ℕ) (hn : 94 ≤ n) :
    16 * dimensionConstant n * (51/20:ℝ)^n < 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) < (n:ℝ)^n := pow_pos hn0 n
  have h := rational_tail_integer n hn
  unfold dimensionConstant
  apply (mul_lt_mul_iff_right₀ hp).mp
  field_simp
  exact h

end MathAndTheory.Gyires.PermutationTransfer
