module
public import MathAndTheory.Mathematics.QPermanent.Finite
public import MathAndTheory.Mathematics.QPermanent.GeneralPolynomial

@[expose] public section

namespace MathAndTheory.QPermanent

/-- The displayed integer example is exactly the one-middle-coordinate family. -/
theorem familyMatrix_one_four_five : familyMatrix 1 4 5 = counterexampleReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [familyMatrix, familyCore, familyIndex, finSumFinEquiv, Fin.addCases,
      counterexampleReal, counterexampleInt, Matrix.fromBlocks]

/-- The entire polynomial, not only its two evaluated values. -/
theorem counterexample_polynomial (q : ℝ) :
    qPermanent counterexampleReal q =
      625 + 25*q^3 + 800*q^5 + 25*q^7 + 256*q^8 - 32*q^9 + q^10 := by
  rw [← familyMatrix_one_four_five, qPermanent_family_formula]
  norm_num
  ring

theorem counterexample_eq_familyPolynomial :
    qPermanent counterexampleReal = familyPolynomial 1 16 25 := by
  funext q
  rw [counterexample_polynomial]
  unfold familyPolynomial
  norm_num
  ring

theorem counterexample_hasDerivAt_fifteen :
    HasDerivAt (qPermanent counterexampleReal) (-1563030000) 15 := by
  have h := family_hasDerivAt 1 16 25 15
  rw [← counterexample_eq_familyPolynomial] at h
  norm_num [familyDerivative] at h
  exact h

theorem counterexample_deriv_fifteen :
    deriv (qPermanent counterexampleReal) 15 = -1563030000 :=
  counterexample_hasDerivAt_fifteen.deriv

end MathAndTheory.QPermanent
