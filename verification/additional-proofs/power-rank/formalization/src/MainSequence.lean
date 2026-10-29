import RankPrinciple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Polynomial
namespace PowerRank

/-- The literal rank-thirteen example from the manuscript. -/
def mainSequence (n : ℕ) : ℂ :=
  1 + 2 ^ n + 3 ^ n * (1 - 2 ^ n) ^ 2 + (n : ℂ) * 9 ^ n * (1 + 2 ^ n) ^ 3

def mainBases : Fin 9 → ℂ := ![1, 2, 3, 6, 12, 9, 18, 36, 72]
def mainCoefficients : Fin 9 → ℂ[X] := ![1, 1, 1, C (-2), 1, X, C 3 * X, C 3 * X, X]

theorem mainBases_ne_zero (i : Fin 9) : mainBases i ≠ 0 := by
  fin_cases i <;> norm_num [mainBases]

theorem mainBases_injective : Function.Injective mainBases := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [mainBases] at hij

theorem mainCoefficients_ne_zero (i : Fin 9) : mainCoefficients i ≠ 0 := by
  fin_cases i <;> norm_num [mainCoefficients, C_mul_X_eq_monomial]

set_option maxRecDepth 4096 in
theorem mainSequence_expansion :
    mainSequence = ∑ i, expPoly (mainBases i) (mainCoefficients i) := by
  ext n
  have h6 : (6 : ℂ) ^ n = (2 : ℂ) ^ n * (3 : ℂ) ^ n := by
    rw [← mul_pow]
    norm_num
  have h12 : (12 : ℂ) ^ n = ((2 : ℂ) ^ n) ^ 2 * (3 : ℂ) ^ n := by
    calc
      _ = ((2 : ℂ) ^ 2 * 3) ^ n := by norm_num
      _ = ((2 : ℂ) ^ 2) ^ n * 3 ^ n := mul_pow _ _ _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  have h18 : (18 : ℂ) ^ n = (2 : ℂ) ^ n * (9 : ℂ) ^ n := by
    rw [← mul_pow]
    norm_num
  have h36 : (36 : ℂ) ^ n = ((2 : ℂ) ^ n) ^ 2 * (9 : ℂ) ^ n := by
    calc
      _ = ((2 : ℂ) ^ 2 * 9) ^ n := by norm_num
      _ = ((2 : ℂ) ^ 2) ^ n * 9 ^ n := mul_pow _ _ _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  have h72 : (72 : ℂ) ^ n = ((2 : ℂ) ^ n) ^ 3 * (9 : ℂ) ^ n := by
    calc
      _ = ((2 : ℂ) ^ 3 * 9) ^ n := by norm_num
      _ = ((2 : ℂ) ^ 3) ^ n * 9 ^ n := mul_pow _ _ _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 n]
  simp [mainSequence, mainBases, mainCoefficients, expPoly, Fin.sum_univ_succ,
    h6, h12, h18, h36, h72]
  ring

/-- The full displayed initial characteristic polynomial, over the complex field. -/
def initialCharacteristic : ℂ[X] :=
  (X - 1) * (X - 2) * (X - 3) * (X - 6) * (X - 12) *
    (X - 9) ^ 2 * (X - 18) ^ 2 * (X - 36) ^ 2 * (X - 72) ^ 2

theorem characteristicProduct_main :
    characteristicProduct mainBases mainCoefficients = initialCharacteristic := by
  norm_num [characteristicProduct, mainBases, mainCoefficients, initialCharacteristic,
    Fin.prod_univ_succ, natDegree_C_mul_X]
  simp only [map_ofNat]
  ring

/-- The rank-thirteen example has the claimed exact complex minimal polynomial. -/
theorem mainSequence_minimalCharacteristic :
    MinimalCharacteristic initialCharacteristic mainSequence := by
  rw [mainSequence_expansion, ← characteristicProduct_main]
  exact minimalCharacteristic_expPoly_sum mainBases mainBases_ne_zero mainBases_injective
    mainCoefficients mainCoefficients_ne_zero

/-- This is a least eventual recurrence order, not just an annihilator upper bound. -/
theorem mainSequence_rank_thirteen : HasRecurrenceRank mainSequence 13 := by
  have h := hasRecurrenceRank_expPoly_sum mainBases mainBases_ne_zero mainBases_injective
    mainCoefficients mainCoefficients_ne_zero
  rw [← mainSequence_expansion] at h
  convert h using 1
  norm_num [mainCoefficients, Fin.sum_univ_succ, natDegree_C_mul_X]

end PowerRank
