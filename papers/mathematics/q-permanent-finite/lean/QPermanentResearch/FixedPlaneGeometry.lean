import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FinCases

/-!
Finite-dimensional geometry used in the rank-two stationary-point argument.
These are matrix identities, independent of any measure, limiting procedure,
or q-permanent counterexample.
-/

namespace QPermanentResearch

/-- A linear map fixing the columns of a nonsingular square matrix is identity. -/
theorem matrix_eq_one_of_fix_nonsingular_columns
    {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S B : Matrix ι ι K) (hdet : B.det ≠ 0) (hfix : S * B = B) : S = 1 := by
  have hunit : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  apply hunit.mul_right_cancel
  simpa only [one_mul] using hfix

/-- In dimension two, two fixed vectors with nonzero coordinate determinant
force the entire matrix to be identity. No symmetry assumption is needed. -/
theorem matrix_two_independent_fixed_vectors_eq_one
    {K : Type*} [Field K] (S : Matrix (Fin 2) (Fin 2) K)
    (u v : Fin 2 → K) (hu : S.mulVec u = u) (hv : S.mulVec v = v)
    (hind : u 0 * v 1 - u 1 * v 0 ≠ 0) : S = 1 := by
  classical
  let B : Matrix (Fin 2) (Fin 2) K := fun i j => if j = 0 then u i else v i
  apply matrix_eq_one_of_fix_nonsingular_columns S B
  · simpa [B, Matrix.det_fin_two, mul_comm] using hind
  · ext i j
    fin_cases j
    · simpa [B, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hu i
    · simpa [B, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i

/-- The real and imaginary parts of a fixed complex vector are fixed by the
original real matrix. A nonzero real-imaginary determinant then gives identity. -/
theorem real_matrix_non_phase_real_fixed_vector_eq_one
    (S : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℂ)
    (hfix : (S.map Complex.ofReal).mulVec z = z)
    (hind : (z 0).re * (z 1).im - (z 1).re * (z 0).im ≠ 0) : S = 1 := by
  apply matrix_two_independent_fixed_vectors_eq_one S
    (fun i => (z i).re) (fun i => (z i).im)
  · ext i
    have h := congrArg Complex.re (congrFun hfix i)
    simpa [Matrix.mulVec, dotProduct, Complex.mul_re] using h
  · ext i
    have h := congrArg Complex.im (congrFun hfix i)
    simpa [Matrix.mulVec, dotProduct, Complex.mul_im] using h
  · exact hind

end QPermanentResearch
