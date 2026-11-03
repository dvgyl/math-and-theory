import CompanionPolynomial
import Mathlib.LinearAlgebra.Determinant

/-!
# The companion polynomial in the original matrix coordinates

Determinants are invariant under a change of basis.  Applying that theorem to
the operator `(z • 1 - H)^2 - (x ↦ ⟪g,x⟫ • g)` identifies the polynomial of
the original six-by-six companion with the spectral secular polynomial.
Neither diagonalizability nor a change-of-basis matrix is assumed.
-/

noncomputable section
open scoped BigOperators Matrix
namespace FilteredF3

section RankOne
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realRankOne (g : E) : E →ₗ[ℝ] E where
  toFun x := inner (𝕜 := ℝ) g x • g
  map_add' x y := by simp [inner_add_right, add_smul]
  map_smul' c x := by simp [inner_smul_right, mul_smul]

theorem realRankOne_toMatrix (b : OrthonormalBasis ι ℝ E) (g : E) :
    LinearMap.toMatrix b.toBasis b.toBasis (realRankOne g) =
      Matrix.vecMulVec (orthoCoordinates b g) (orthoCoordinates b g) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, realRankOne, LinearMap.coe_mk,
    AddHom.coe_mk, map_smul, PiLp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.of_apply, orthoCoordinates, OrthonormalBasis.repr_apply_apply]
  rw [real_inner_comm g (b j)]
  ring

end RankOne

section SelfAdjointMatrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {n : ℕ} [NeZero n]

theorem selfAdjoint_toMatrix (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) :
    LinearMap.toMatrix (hH.eigenvectorBasis hn).toBasis
      (hH.eigenvectorBasis hn).toBasis H = Matrix.diagonal (hH.eigenvalues hn) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, hH.eigenvectorBasis_apply_self_apply,
    RCLike.ofReal_real_eq_id, id_eq, OrthonormalBasis.repr_self]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, hij, Ne.symm hij]

end SelfAdjointMatrix

section Three

theorem matrix_secular_determinant_three
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsHermitian) (g : Fin 3 → ℝ) (z : ℝ) :
    ((z • 1 - H) * (z • 1 - H) - Matrix.vecMulVec g g).det =
      secularPolynomial (matrixEigenvalues H hH) (matrixCoordinates H hH g) z := by
  let HE := H.toEuclideanLin
  let gE : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm g
  let hs : HE.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hH
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let b := hs.eigenvectorBasis hn
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let L : Module.End ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (z • 1 - HE) * (z • 1 - HE) - realRankOne gE
  have heH : LinearMap.toMatrix e.toBasis e.toBasis HE = H := by
    change LinearMap.toMatrix e.toBasis e.toBasis
      (Matrix.toLin e.toBasis e.toBasis H) = H
    exact LinearMap.toMatrix_toLin e.toBasis e.toBasis H
  have heG : orthoCoordinates e gE = g := rfl
  have heL : LinearMap.toMatrix e.toBasis e.toBasis L =
      (z • 1 - H) * (z • 1 - H) - Matrix.vecMulVec g g := by
    simp only [L, map_sub, LinearMap.toMatrix_mul, map_smul,
      LinearMap.toMatrix_one, heH, realRankOne_toMatrix, heG]
  have hbH : LinearMap.toMatrix b.toBasis b.toBasis HE =
      Matrix.diagonal (matrixEigenvalues H hH) := by
    exact selfAdjoint_toMatrix HE hs hn
  have hbG : orthoCoordinates b gE = matrixCoordinates H hH g := rfl
  have hbL : LinearMap.toMatrix b.toBasis b.toBasis L =
      Matrix.diagonal (fun i => (z - matrixEigenvalues H hH i)^2) -
        Matrix.vecMulVec (matrixCoordinates H hH g) (matrixCoordinates H hH g) := by
    simp only [L, map_sub, LinearMap.toMatrix_mul, map_smul,
      LinearMap.toMatrix_one, hbH, realRankOne_toMatrix, hbG]
    have hd : z • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        Matrix.diagonal (matrixEigenvalues H hH) =
        Matrix.diagonal (fun i => z - matrixEigenvalues H hH i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal_apply, Matrix.one_apply]
      · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    rw [hd, Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  rw [← heL, LinearMap.det_toMatrix_eq_det_toMatrix e.toBasis b.toBasis,
    hbL, diagonal_rank_one_determinant_three]

/-- The exact sextic for the original, arbitrary symmetric matrix. -/
theorem original_companion_sextic_three
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsHermitian) (g : Fin 3 → ℝ) (z : ℝ) :
    (z • (1 : Matrix (Sum (Fin 3) (Fin 3)) (Sum (Fin 3) (Fin 3)) ℝ) -
      companionMatrix H g).det =
        secularPolynomial (matrixEigenvalues H hH) (matrixCoordinates H hH g) z := by
  rw [companion_characteristic_determinant, matrix_secular_determinant_three H hH]

/-- A greatest real characteristic root exists, including every singular case,
and is exactly the root appearing in the closed-form optimization theorem. -/
theorem original_companion_largest_real_root
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsHermitian) (g : Fin 3 → ℝ) :
    IsGreatest {z : ℝ | (z • (1 : Matrix (Sum (Fin 3) (Fin 3))
      (Sum (Fin 3) (Fin 3)) ℝ) - companionMatrix H g).det = 0}
      (largestRealRoot (matrixEigenvalues H hH) (matrixCoordinates H hH g)) := by
  simpa only [original_companion_sextic_three H hH] using
    largestRealRoot_spec (matrixEigenvalues H hH) (matrixCoordinates H hH g)

end Three
end FilteredF3
