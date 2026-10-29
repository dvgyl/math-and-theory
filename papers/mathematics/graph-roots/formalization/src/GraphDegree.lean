import NonzeroRoots

noncomputable section
namespace SquareFlowerCompletion.Extremal
open Polynomial

theorem graphPolynomial_factorization (n : ℕ) :
    graphPolynomial n = X^n * bracketPolynomial n := by
  apply Polynomial.funext
  intro z
  simp [Counting.eval_complexDominationPolynomial, bracketPolynomial]

theorem graphPolynomial_natDegree (n : ℕ) : (graphPolynomial n).natDegree = 3*n+1 := by
  rw [graphPolynomial_factorization, natDegree_mul (pow_ne_zero _ X_ne_zero)
    (by intro h; have ht := bracket_natDegree n; simp [h] at ht),
    natDegree_X_pow, bracket_natDegree]
  omega

theorem graphPolynomial_origin_multiplicity (n : ℕ) :
    (graphPolynomial n).rootMultiplicity 0 = n+1 := by
  have hp := (bracketPolynomial n).X_mul_divX_add
  rw [bracket_coeff_zero, map_zero, add_zero] at hp
  have hfactor : graphPolynomial n = X^(n+1) * (bracketPolynomial n).divX := by
    calc
      graphPolynomial n = X^n * bracketPolynomial n := graphPolynomial_factorization n
      _ = X^n * (X * (bracketPolynomial n).divX) := congrArg (X^n * ·) hp.symm
      _ = _ := by rw [pow_succ]; ring
  have hq : ¬ (bracketPolynomial n).divX.IsRoot 0 := by
    rw [Polynomial.IsRoot.def, bracket_divX_eval_zero]
    have hr : (0:ℝ) < 3^n + 3*(n:ℝ) := by positivity
    exact_mod_cast hr.ne'
  rw [hfactor, rootMultiplicity_mul (by rw [← hfactor]; exact graphPolynomial_ne_zero n),
    rootMultiplicity_eq_zero hq, add_zero]
  simpa using (rootMultiplicity_X_sub_C_pow (R := ℂ) 0 (n+1))

#print axioms graphPolynomial_natDegree
#print axioms graphPolynomial_origin_multiplicity
end SquareFlowerCompletion.Extremal
