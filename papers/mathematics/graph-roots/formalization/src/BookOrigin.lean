import BookPolynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Polynomial
namespace BookCompletion

def quotientPolynomial (n : ℕ) : Polynomial ℝ :=
  (2*X+1)*X^(n-2)*(X+2)^n + (1+X)^(2*n) - 2*X^(n-2)

theorem realPolynomial_factor (n : ℕ) (hn : 2 ≤ n) :
    realPolynomial n = (X : Polynomial ℝ)^2 * quotientPolynomial n := by
  have hp : (X : Polynomial ℝ)^n = X^2 * X^(n-2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [realPolynomial_formula n (by omega)]
  have hq : (X : Polynomial ℝ)^2+2*X = X*(X+2) := by ring
  rw [hq, mul_pow, hp]
  unfold quotientPolynomial
  ring

theorem quotientPolynomial_eval_zero (n : ℕ) (hn : 2 ≤ n) :
    (quotientPolynomial n).eval 0 = if n=2 then 3 else 1 := by
  by_cases h : n=2
  · subst n
    norm_num [quotientPolynomial]
  · have he : n-2 ≠ 0 := by omega
    simp [quotientPolynomial, he, h]

theorem quotientPolynomial_not_root (n : ℕ) (hn : 2 ≤ n) :
    ¬ (quotientPolynomial n).IsRoot 0 := by
  rw [Polynomial.IsRoot.def, quotientPolynomial_eval_zero n hn]
  split <;> norm_num

theorem realPolynomial_origin_multiplicity (n : ℕ) (hn : 1 ≤ n) :
    (realPolynomial n).rootMultiplicity 0 = 2 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    rw [realPolynomial_one]
    have hq : ¬ (((X+2)^2+2 : Polynomial ℝ).IsRoot 0) := by
      simp [Polynomial.IsRoot.def]
      norm_num
    have hz : (X^2 * ((X+2)^2+2) : Polynomial ℝ) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ X_ne_zero)
      intro hzero
      have := congrArg (fun p : Polynomial ℝ => p.eval 0) hzero
      norm_num at this
    rw [rootMultiplicity_mul hz, rootMultiplicity_eq_zero hq, add_zero]
    simpa using (rootMultiplicity_X_sub_C_pow (R := ℝ) 0 2)
  · have hn2 : 2 ≤ n := by omega
    have hq := quotientPolynomial_not_root n hn2
    have hz : ((X : Polynomial ℝ)^2 * quotientPolynomial n) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ X_ne_zero)
      intro hzero
      apply hq
      simp [hzero, Polynomial.IsRoot.def]
    rw [realPolynomial_factor n hn2, rootMultiplicity_mul hz,
      rootMultiplicity_eq_zero hq, add_zero]
    simpa using (rootMultiplicity_X_sub_C_pow (R := ℝ) 0 2)

theorem realPolynomial_one_roots (x : ℝ) :
    (realPolynomial 1).IsRoot x ↔ x=0 := by
  rw [Polynomial.IsRoot.def, realPolynomial_one]
  simp only [eval_mul, eval_pow, eval_X, eval_add, eval_ofNat]
  have hpos : 0 < (x+2)^2+2 := by positivity
  rw [mul_eq_zero]
  simp [ne_of_gt hpos]

#print axioms realPolynomial_factor
#print axioms quotientPolynomial_eval_zero
#print axioms quotientPolynomial_not_root
#print axioms realPolynomial_origin_multiplicity
#print axioms realPolynomial_one_roots
end BookCompletion
