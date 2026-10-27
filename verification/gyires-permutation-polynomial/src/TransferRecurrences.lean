module

public import TransferOnePower4
public import TransferTwoPower6

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem one_trace_0 (d e f : ℝ) :
    Matrix.trace (transferOne d e f ^ 0) = 4 := by norm_num [Matrix.trace_one]


theorem one_trace_1 (d e f : ℝ) :
    Matrix.trace (transferOne d e f ^ 1) = e := by norm_num [Matrix.trace, transferOne, Fin.sum_univ_succ]


theorem one_trace_2 (d e f : ℝ) :
    Matrix.trace (transferOne d e f ^ 2) = 2*d*f + e^2 := by rw [one_pow_2]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem one_trace_3 (d e f : ℝ) :
    Matrix.trace (transferOne d e f ^ 3) = 3*d*e*f + e^3 + 3*e*f^2 := by rw [one_pow_3]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem two_trace_0 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 0) = 6 := by norm_num [Matrix.trace_one]


theorem two_trace_1 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 1) = d := by norm_num [Matrix.trace, transferTwo, Fin.sum_univ_succ]


theorem two_trace_2 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 2) = d^2 + 2*e^2 + 2*f^2 := by rw [two_pow_2]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem two_trace_3 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 3) = d^3 + 3*d*e^2 + 3*d*f^2 + 6*e^2*f := by rw [two_pow_3]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem two_trace_4 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 4) = d^4 + 4*d^2*e^2 + 4*d^2*f^2 + 8*d*e^2*f + 2*e^4 + 8*e^2*f^2 + 6*f^4 := by rw [two_pow_4]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem two_trace_5 (d e f : ℝ) :
    Matrix.trace (transferTwo d e f ^ 5) = d^5 + 5*d^3*e^2 + 5*d^3*f^2 + 10*d^2*e^2*f + 5*d*e^4 + 15*d*e^2*f^2 + 5*d*f^4 + 10*e^4*f + 10*e^2*f^3 := by rw [two_pow_5]; norm_num [Matrix.trace, Fin.sum_univ_succ]; ring


theorem one_annihilator (d e f : ℝ) :
    transferOne d e f ^ 4 = e • (transferOne d e f ^ 3) +
      (d*f) • (transferOne d e f ^ 2) + (e*f^2) • transferOne d e f +
      f^4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [one_pow_4, one_pow_3, one_pow_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferOne, Matrix.one_apply] <;> ring

theorem two_annihilator (d e f : ℝ) :
    transferTwo d e f ^ 6 = d • (transferTwo d e f ^ 5) +
      (e^2+f^2) • (transferTwo d e f ^ 4) + (2*e^2*f) • (transferTwo d e f ^ 3) +
      (e^2*f^2+f^4) • (transferTwo d e f ^ 2) - (d*f^4) • transferTwo d e f -
      f^6 • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  rw [two_pow_6, two_pow_5, two_pow_4, two_pow_3, two_pow_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferTwo, Matrix.one_apply] <;> ring

theorem one_trace_recurrence (d e f : ℝ) (n : ℕ) :
    Matrix.trace (transferOne d e f ^ (n+4)) =
      e * Matrix.trace (transferOne d e f ^ (n+3)) +
      (d*f) * Matrix.trace (transferOne d e f ^ (n+2)) +
      (e*f^2) * Matrix.trace (transferOne d e f ^ (n+1)) +
      f^4 * Matrix.trace (transferOne d e f ^ n) := by
  have h := congrArg (fun M => Matrix.trace (M * transferOne d e f ^ n))
    (one_annihilator d e f)
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, ← pow_add, ← pow_succ'] at h
  simpa [Nat.add_comm] using h

theorem two_trace_recurrence (d e f : ℝ) (n : ℕ) :
    Matrix.trace (transferTwo d e f ^ (n+6)) =
      d * Matrix.trace (transferTwo d e f ^ (n+5)) +
      (e^2+f^2) * Matrix.trace (transferTwo d e f ^ (n+4)) +
      (2*e^2*f) * Matrix.trace (transferTwo d e f ^ (n+3)) +
      (e^2*f^2+f^4) * Matrix.trace (transferTwo d e f ^ (n+2)) -
      (d*f^4) * Matrix.trace (transferTwo d e f ^ (n+1)) -
      f^6 * Matrix.trace (transferTwo d e f ^ n) := by
  have h := congrArg (fun M => Matrix.trace (M * transferTwo d e f ^ n))
    (two_annihilator d e f)
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    ← pow_add, ← pow_succ'] at h
  simpa [Nat.add_comm] using h

end MathAndTheory.Gyires.PermutationFinite
