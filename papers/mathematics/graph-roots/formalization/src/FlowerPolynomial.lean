import FlowerCounting
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open Polynomial
namespace SquareFlowerCompletion.Counting

theorem dominationPolynomial_expanded (n : ℕ) :
    dominationPolynomial (flower n) =
      (X : P) * (X^3+3*X^2+3*X)^n + (X^3+3*X^2+X)^n - X^n := by
  rw [dominationPolynomial_eq_rootGF, rootGF_factor, branchGF_true, branchGF_false,
    branchNoEnd_eq]

theorem dominationPolynomial_formula (n : ℕ) :
    dominationPolynomial (flower n) =
      (X : P)^n * (X*(X^2+3*X+3)^n + (X^2+3*X+1)^n - 1) := by
  rw [dominationPolynomial_expanded]
  have ha : (X : P)^3+3*X^2+3*X = X*(X^2+3*X+3) := by ring
  have hb : (X : P)^3+3*X^2+X = X*(X^2+3*X+1) := by ring
  rw [ha,hb,mul_pow,mul_pow]
  ring

theorem dominationPolynomial_zero : dominationPolynomial (flower 0) = (X : P) := by
  rw [dominationPolynomial_formula]
  simp

def complexDominationPolynomial (n : ℕ) : Polynomial ℂ :=
  (dominationPolynomial (flower n)).map (Int.castRingHom ℂ)

theorem eval_complexDominationPolynomial (n : ℕ) (z : ℂ) :
    (complexDominationPolynomial n).eval z =
      z^n * (z*(z^2+3*z+3)^n + (z^2+3*z+1)^n - 1) := by
  rw [complexDominationPolynomial, dominationPolynomial_formula]
  simp

theorem eval_eq_zero_iff_bracket {n : ℕ} {z : ℂ} (hz : z ≠ 0) :
    (complexDominationPolynomial n).eval z = 0 ↔
      z*(z^2+3*z+3)^n + (z^2+3*z+1)^n - 1 = 0 := by
  rw [eval_complexDominationPolynomial, mul_eq_zero]
  simp [pow_ne_zero n hz]

#print axioms dominationPolynomial_expanded
#print axioms dominationPolynomial_formula
#print axioms dominationPolynomial_zero
#print axioms eval_complexDominationPolynomial
#print axioms eval_eq_zero_iff_bracket
end SquareFlowerCompletion.Counting
