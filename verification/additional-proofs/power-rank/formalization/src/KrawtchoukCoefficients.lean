import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

noncomputable section
open Polynomial
namespace PowerRank

/-- Actual coefficients of the signed binomial polynomial. -/
def layerCoefficient (N r k : ℕ) : ℚ :=
  (((1 + X : ℚ[X]) ^ (N - r)) * (1 - X) ^ r).coeff k

theorem coeff_euler_derivative (P : ℚ[X]) (k : ℕ) :
    (X * P.derivative).coeff k = (k : ℚ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- A polynomial identity supplies the Krawtchouk recurrence without a duality assumption. -/
theorem signed_binomial_differential_identity (m r : ℕ) :
    C (m + 1 : ℚ) * (1 + X) ^ m * (1 - X) ^ (r + 2) =
      C (m + r + 2 : ℚ) * ((1 + X) ^ (m + 1) * (1 - X) ^ (r + 1)) -
      C 2 * X * derivative ((1 + X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (r + 1)) -
      C (r + 1 : ℚ) * (1 + X) ^ (m + 2) * (1 - X) ^ r := by
  rw [derivative_mul, derivative_pow, derivative_pow]
  simp only [derivative_add, derivative_sub, derivative_one, derivative_X,
    zero_add, zero_sub, Nat.add_sub_cancel, mul_one, mul_neg_one]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one, map_ofNat]
  ring

theorem signed_binomial_first_identity (m : ℕ) :
    C (m + 1 : ℚ) * (1 + X) ^ m * (1 - X) =
      C (m + 1 : ℚ) * (1 + X) ^ (m + 1) -
        C 2 * X * derivative ((1 + X : ℚ[X]) ^ (m + 1)) := by
  rw [derivative_pow]
  simp only [derivative_add, derivative_one, derivative_X, zero_add,
    Nat.add_sub_cancel, mul_one]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one, map_ofNat]
  ring

theorem layerCoefficient_zero (N k : ℕ) :
    layerCoefficient N 0 k = (N.choose k : ℚ) := by
  simp [layerCoefficient, coeff_one_add_X_pow]

/-- Coefficient recurrence, including all coefficient endpoints. -/
theorem layerCoefficient_recurrence (N r k : ℕ) (hN : r + 2 ≤ N) :
    ((N : ℚ) - (r + 1)) * layerCoefficient N (r + 2) k =
      ((N : ℚ) - 2 * k) * layerCoefficient N (r + 1) k -
        (r + 1) * layerCoefficient N r k := by
  let m := N - (r + 2)
  have hm : N = m + r + 2 := by dsimp [m]; omega
  have hp := congrArg (fun P : ℚ[X] => P.coeff k)
    (signed_binomial_differential_identity m r)
  rw [show C 2 * X * derivative ((1 + X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (r + 1)) =
      C 2 * (X * derivative ((1 + X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (r + 1))) by ring] at hp
  simp only [mul_assoc, coeff_sub, coeff_C_mul, coeff_euler_derivative] at hp
  have h0 : N - r = m + 2 := by omega
  have h1 : N - (r + 1) = m + 1 := by omega
  have h2 : N - (r + 2) = m := by omega
  unfold layerCoefficient
  rw [h0, h1, h2]
  have hcast : (N : ℚ) = m + r + 2 := by exact_mod_cast hm
  rw [hcast]
  linear_combination hp

theorem layerCoefficient_first (N k : ℕ) (hN : 1 ≤ N) :
    (N : ℚ) * layerCoefficient N 1 k =
      ((N : ℚ) - 2 * k) * (N.choose k : ℚ) := by
  let m := N - 1
  have hm : N = m + 1 := by dsimp [m]; omega
  have hp := congrArg (fun P : ℚ[X] => P.coeff k) (signed_binomial_first_identity m)
  rw [show C 2 * X * derivative ((1 + X : ℚ[X]) ^ (m + 1)) =
      C 2 * (X * derivative ((1 + X : ℚ[X]) ^ (m + 1))) by ring] at hp
  simp only [mul_assoc, coeff_sub, coeff_C_mul, coeff_euler_derivative] at hp
  have hcoeff : ((1 + X : ℚ[X]) ^ (m + 1)).coeff k = (N.choose k : ℚ) := by
    rw [← hm, coeff_one_add_X_pow]
  rw [hcoeff] at hp
  have hcast : (N : ℚ) = m + 1 := by exact_mod_cast hm
  unfold layerCoefficient
  rw [show N - 1 = m by rfl, pow_one, hcast]
  linear_combination hp

/-- Exact quadratic coefficient identity in a denominator-free form. -/
theorem layerCoefficient_quadratic (N k : ℕ) (hN : 2 ≤ N) :
    (N : ℚ) * (N - 1) * layerCoefficient N 2 k =
      (N.choose k : ℚ) * (((N : ℚ) - 2 * k) ^ 2 - N) := by
  have h0 := layerCoefficient_first N k (by omega)
  have h1 := layerCoefficient_recurrence N 0 k (by omega)
  rw [layerCoefficient_zero] at h1
  norm_num at h1
  linear_combination (N : ℚ) * h1 + ((N : ℚ) - 2 * k) * h0

theorem layerCoefficient_quadratic_formula (N k : ℕ) (hN : 2 ≤ N) :
    layerCoefficient N 2 k =
      (N.choose k : ℚ) * (((N : ℚ) - 2 * k) ^ 2 - N) / ((N : ℚ) * (N - 1)) := by
  have h0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1 : (N : ℚ) - 1 ≠ 0 := by
    have hh : (2 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  apply (eq_div_iff (mul_ne_zero h0 h1)).mpr
  linear_combination layerCoefficient_quadratic N k hN

private theorem sixth_from_recurrence (N t b L1 L2 L3 L4 L5 L6 : ℚ)
    (hN : 6 ≤ N) (hs : t ^ 2 = N)
    (h0 : N * L1 = t * b)
    (h1 : (N - 1) * L2 = t * L1 - b)
    (h2 : (N - 2) * L3 = t * L2 - 2 * L1)
    (h3 : (N - 3) * L4 = t * L3 - 3 * L2)
    (h4 : (N - 4) * L5 = t * L4 - 4 * L3)
    (h5 : (N - 5) * L6 = t * L5 - 5 * L4) :
    L6 = b * 16 / ((N - 2) * (N - 3) * (N - 5)) := by
  have hn0 : N ≠ 0 := by linarith
  have hn1 : N - 1 ≠ 0 := by linarith
  have hn2 : N - 2 ≠ 0 := by linarith
  have hn3 : N - 3 ≠ 0 := by linarith
  have hn4 : N - 4 ≠ 0 := by linarith
  have hn5 : N - 5 ≠ 0 := by linarith
  have e1 : L1 = t * b / N := (eq_div_iff hn0).mpr (by linear_combination h0)
  have e2 : L2 = 0 := by
    have h : N * (N - 1) * L2 = 0 := by
      linear_combination N * h1 + t * h0 + b * hs
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn0 hn1)
  have e3 : L3 = -2 * t * b / (N * (N - 2)) := by
    have e : L3 = (t * L2 - 2 * L1) / (N - 2) :=
      (eq_div_iff hn2).mpr (by linear_combination h2)
    rw [e, e2, e1]
    field_simp
    ring
  have e4 : L4 = -2 * b / ((N - 2) * (N - 3)) := by
    have e : L4 = (t * L3 - 3 * L2) / (N - 3) :=
      (eq_div_iff hn3).mpr (by linear_combination h3)
    rw [e, e3, e2]
    field_simp
    linear_combination -2 * b * hs
  have e5 : L5 = 6 * t * b / (N * (N - 2) * (N - 3)) := by
    have e : L5 = (t * L4 - 4 * L3) / (N - 4) :=
      (eq_div_iff hn4).mpr (by linear_combination h4)
    rw [e, e4, e3]
    field_simp
    ring
  have e : L6 = (t * L5 - 5 * L4) / (N - 5) :=
    (eq_div_iff hn5).mpr (by linear_combination h5)
  rw [e, e5, e4]
  field_simp
  linear_combination 6 * b * hs

/-- Exact nonzero next-degree coefficient at every exceptional quadratic zero. -/
theorem layerCoefficient_sixth_formula (N k : ℕ) (hN : 6 ≤ N)
    (hs : ((N : ℚ) - 2 * k) ^ 2 = N) :
    layerCoefficient N 6 k =
      (N.choose k : ℚ) * 16 / (((N : ℚ) - 2) * (N - 3) * (N - 5)) := by
  have h0 := layerCoefficient_first N k (by omega)
  have h1 := layerCoefficient_recurrence N 0 k (by omega)
  have h2 := layerCoefficient_recurrence N 1 k (by omega)
  have h3 := layerCoefficient_recurrence N 2 k (by omega)
  have h4 := layerCoefficient_recurrence N 3 k (by omega)
  have h5 := layerCoefficient_recurrence N 4 k (by omega)
  rw [layerCoefficient_zero] at h1
  norm_num at h1 h2 h3 h4 h5
  exact sixth_from_recurrence _ _ _ _ _ _ _ _ _ (by exact_mod_cast hN) hs h0 h1 h2 h3 h4 h5

theorem layerCoefficient_sixth_positive (N k : ℕ) (hN : 6 ≤ N) (hk : k ≤ N)
    (hs : ((N : ℚ) - 2 * k) ^ 2 = N) : 0 < layerCoefficient N 6 k := by
  rw [layerCoefficient_sixth_formula N k hN hs]
  have hb : (0 : ℚ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have h2 : (0 : ℚ) < N - 2 := by
    have hh : (6 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have h3 : (0 : ℚ) < N - 3 := by
    have hh : (6 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have h5 : (0 : ℚ) < N - 5 := by
    have hh : (6 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  positivity

end PowerRank
