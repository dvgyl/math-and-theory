import BookCounting
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open Polynomial
open SquareFlowerCompletion.Counting
namespace BookCompletion

theorem dominationPolynomial_expanded (n : ℕ) :
    dominationPolynomial (book n) =
      (2*X+1 : P)*(X^2+2*X)^n + X^2*(1+X)^(2*n) - 2*X^n + (0 : P)^n := by
  rw [dominationPolynomial_eq_hubsGF, hubsGF_factor, noHubsGF_eq,
    pairGF_eq, nonemptyGF_eq, ← pow_mul]
  ring

theorem dominationPolynomial_formula (n : ℕ) (hn : 1 ≤ n) :
    dominationPolynomial (book n) =
      (2*X+1 : P)*(X^2+2*X)^n + X^2*(1+X)^(2*n) - 2*X^n := by
  rw [dominationPolynomial_expanded]
  simp [zero_pow (by omega : n ≠ 0)]

theorem dominationPolynomial_zero : dominationPolynomial (book 0) = (X : P)^2+2*X := by
  rw [dominationPolynomial_expanded]
  norm_num
  ring

theorem dominationPolynomial_one :
    dominationPolynomial (book 1) = (X : P)^2*(X^2+4*X+6) := by
  rw [dominationPolynomial_formula 1 (by omega)]
  norm_num
  ring

def realPolynomial (n : ℕ) : Polynomial ℝ :=
  (dominationPolynomial (book n)).map (Int.castRingHom ℝ)

theorem realPolynomial_formula (n : ℕ) (hn : 1 ≤ n) :
    realPolynomial n =
      (2*X+1 : Polynomial ℝ)*(X^2+2*X)^n + X^2*(1+X)^(2*n) - 2*X^n := by
  rw [realPolynomial, dominationPolynomial_formula n hn]
  simp

theorem realPolynomial_one :
    realPolynomial 1 = (X : Polynomial ℝ)^2*((X+2)^2+2) := by
  rw [realPolynomial, dominationPolynomial_one]
  simp
  ring

theorem eval_realPolynomial (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (realPolynomial n).eval x =
      (2*x+1)*(x^2+2*x)^n + x^2*(1+x)^(2*n) - 2*x^n := by
  rw [realPolynomial_formula n hn]
  simp

#print axioms dominationPolynomial_expanded
#print axioms dominationPolynomial_formula
#print axioms dominationPolynomial_zero
#print axioms dominationPolynomial_one
#print axioms realPolynomial_formula
#print axioms realPolynomial_one
#print axioms eval_realPolynomial
end BookCompletion
