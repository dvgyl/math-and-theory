import DominationULC.ConditionalSequences
import DominationULC.Euler
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace DominationULC

theorem path_endpoint_mono (a m : ℕ) (ham : a ≤ m) (k : ℕ) (N : ℤ) :
    (tpart a * part a * part m ^ k) N *
        (part a ^ 2 * part m ^ (k + 2)) N ≤
      (tpart a * part a * part m ^ (k + 1)) N *
        (part a ^ 2 * part m ^ (k + 1)) N := by
  have h := conditional_coefficient_mono (part a * part m) (part a * part m ^ k)
    (convolution_nonnegative (part_nonnegative a) (part_nonnegative m))
    (tp2_mul (part_tp2 a) (tp2_pow (part_tp2 m) k)) m N (a : ℤ)
  have hc : cutoff (part a * part m) (a : ℤ) = tpart a := cut_part_mul a m ham
  rw [hc] at h
  simpa only [pow_succ, pow_two, pow_zero, mul_one, one_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem path_interior_mono (a m k : ℕ) (N : ℤ) :
    (tpart m * part a ^ 2 * part m ^ k) N *
        (part a ^ 2 * part m ^ (k + 3)) N ≤
      (tpart m * part a ^ 2 * part m ^ (k + 1)) N *
        (part a ^ 2 * part m ^ (k + 2)) N := by
  have h := conditional_coefficient_mono (part m * part m) (part a ^ 2 * part m ^ k)
    (convolution_nonnegative (part_nonnegative m) (part_nonnegative m))
    (tp2_mul (tp2_pow (part_tp2 a) 2) (tp2_pow (part_tp2 m) k)) m N (m : ℤ)
  have hc : cutoff (part m * part m) (m : ℤ) = tpart m := cut_part_mul m m le_rfl
  rw [hc] at h
  simpa only [pow_succ, pow_two, pow_zero, mul_one, one_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem path_endpoint_le_interior (a m : ℕ) (ham : a ≤ m) (k : ℕ) (N : ℤ) :
    (tpart a * part a * part m ^ (k + 1)) N ≤
      (tpart m * part a ^ 2 * part m ^ k) N := by
  have h : ((part a * part m ^ k) * (part m * tpart a)) N ≤
      ((part a * part m ^ k) * (part a * tpart m)) N := by
    rw [convolution_apply, convolution_apply]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (endpoint_le_interior a m ham (N-i))
      ((convolution_nonnegative (part_nonnegative a)
        (nonnegative_pow (part_nonnegative m) k)) i)
  simpa only [pow_succ, pow_two, pow_zero, mul_one, one_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Ultra-log-concavity with the ambient path length normalization, for two
endpoint parts of bound `a` and any number of interior parts of bound `m≥a`.
All statements are cross-multiplied and include zero coefficients. -/
theorem path_coeff_ulc (a m : ℕ) (ham : a ≤ m) (N : ℤ) (j : ℕ) :
    ((j + 3 : ℕ) : ℝ) * ((N : ℝ) - ((j + 2 : ℕ) : ℝ)) *
        (part a ^ 2 * part m ^ j) N * (part a ^ 2 * part m ^ (j + 2)) N ≤
      ((j + 2 : ℕ) : ℝ) * ((N : ℝ) - ((j + 3 : ℕ) : ℝ)) *
        ((part a ^ 2 * part m ^ (j + 1)) N) ^ 2 := by
  cases j with
  | zero =>
    have he := path_endpoint_mono a m ham 0 N
    have hei := path_endpoint_le_interior a m ham 0 N
    have hD := (convolution_nonnegative
      (nonnegative_pow (part_nonnegative a) 2) (part_nonnegative m)) N
    simp only [pow_zero, pow_one, mul_one, Nat.zero_add] at he hei
    have hmix := deletion_mixture_two_three_cross_mul hD he hei
    simp only [tpart] at hmix
    have hp := path_euler_two (part a) N
    have hp' := path_euler (part a) (part m) 0 N
    simp only [pow_zero, pow_one, mul_one, Nat.zero_add, Nat.cast_one,
      Nat.cast_ofNat, one_mul] at hp hp'
    simp only [Nat.zero_add, Nat.cast_ofNat, pow_zero, pow_one, mul_one]
    have hscaled := mul_le_mul_of_nonneg_left hmix (by norm_num : (0 : ℝ) ≤ 2)
    have hpe := congrArg (fun x : ℝ => 3 * x * (part a ^ 2 * part m ^ 2) N) hp
    have hpe' := congrArg (fun x : ℝ => 2 * x * (part a ^ 2 * part m) N) hp'
    dsimp only at hpe hpe'
    nlinarith only [hscaled, hpe, hpe']
  | succ k =>
    have he := path_endpoint_mono a m ham (k + 1) N
    have hi := path_interior_mono a m k N
    have hei := path_endpoint_le_interior a m ham k N
    have hD := (convolution_nonnegative
      (nonnegative_pow (part_nonnegative a) 2)
      (nonnegative_pow (part_nonnegative m) (k + 3))) N
    have hmix := deletion_mixture_cross_mul
      (k := ((k + 3 : ℕ) : ℝ))
      (by exact_mod_cast (show 2 ≤ k + 3 by omega))
      hD he hi hei
    simp only [tpart] at hmix
    have hp := path_euler (part a) (part m) k N
    have hp' := path_euler (part a) (part m) (k + 1) N
    have hpe := congrArg
      (fun x : ℝ => ((k + 4 : ℕ) : ℝ) * x * (part a ^ 2 * part m ^ (k + 3)) N) hp
    have hpe' := congrArg
      (fun x : ℝ => ((k + 3 : ℕ) : ℝ) * x * (part a ^ 2 * part m ^ (k + 2)) N) hp'
    simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] at *
    push_cast at hmix hpe hpe' ⊢
    nlinarith only [hmix, hpe, hpe']

end DominationULC
