import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-!
Exact spectral factorization of a shifted real symmetric matrix.

This file uses mathlib's proved finite-dimensional spectral theorem.  It does
not assert that a particular stochastic generator has the required spectrum;
that is the separate rate-defined Gram-matrix obligation.
-/

open scoped BigOperators
open Polynomial

namespace UnicyclicSpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_shift_eq_prod (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (s : ℝ) :
    (s • (1 : Matrix ι ι ℝ) + H).det =
      ∏ i, (s + hH.eigenvalues i) := by
  have hdiag :
      star (hH.eigenvectorUnitary : Matrix ι ι ℝ) * H *
        (hH.eigenvectorUnitary : Matrix ι ι ℝ) =
      Matrix.diagonal hH.eigenvalues := by
    simpa using hH.star_mul_self_mul_eq_diagonal
  have hconj :
      star (hH.eigenvectorUnitary : Matrix ι ι ℝ) *
          (s • (1 : Matrix ι ι ℝ) + H) *
          (hH.eigenvectorUnitary : Matrix ι ι ℝ) =
      s • (1 : Matrix ι ι ℝ) + Matrix.diagonal hH.eigenvalues := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, unitary.coe_star_mul_self, hdiag]
  have hdet := congrArg Matrix.det hconj
  rw [Matrix.det_mul_right_comm, unitary.coe_star_mul_self, Matrix.one_mul] at hdet
  rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_add, Matrix.det_diagonal] at hdet
  simpa only [Matrix.smul_one_eq_diagonal] using hdet

/-- Evaluation of the characteristic polynomial of `-L` is `det(s I + L)`. -/
theorem charpoly_neg_eval (L : Matrix ι ι ℝ) (s : ℝ) :
    (-L).charpoly.eval s = (s • (1 : Matrix ι ι ℝ) + L).det := by
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix]
  simp [Matrix.scalar, Matrix.smul_one_eq_diagonal, Pi.algebraMap_def]

theorem charpoly_neg_eq_spectral_product
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    (-H).charpoly = ∏ i, (X + C (hH.eigenvalues i)) := by
  apply Polynomial.funext
  intro s
  rw [charpoly_neg_eval, det_shift_eq_prod H hH]
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]

/-- A pointwise determinant shift gives the exact polynomial factorization. -/
theorem polynomial_factorization_of_det_shift
    (L H : Matrix ι ι ℝ) (hH : H.IsHermitian) (d : ℝ)
    (hshift : ∀ s : ℝ,
      (s • (1 : Matrix ι ι ℝ) + H).det =
      (s • (1 : Matrix ι ι ℝ) + L).det + d) :
    (-L).charpoly + C d = ∏ i, (X + C (hH.eigenvalues i)) := by
  apply Polynomial.funext
  intro s
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  rw [charpoly_neg_eval, ← hshift, det_shift_eq_prod H hH]
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]

#print axioms det_shift_eq_prod
#print axioms charpoly_neg_eval
#print axioms charpoly_neg_eq_spectral_product
#print axioms polynomial_factorization_of_det_shift

end UnicyclicSpectral
