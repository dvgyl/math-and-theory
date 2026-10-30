module

public import MatCP1Converse.NearbySurjection
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace MatCP1Converse

variable {F n m p : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p] [DecidableEq n]

/-- Standard-coordinate matrices of mutually inverse linear equivalences are inverses. -/
theorem toMatrix_equiv_mul_symm (S : (n → F) ≃ₗ[F] (n → F)) :
    LinearMap.toMatrix' S.toLinearMap * LinearMap.toMatrix' S.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have h : S.toLinearMap.comp S.symm.toLinearMap = LinearMap.id := by
    ext v
    simp
  rw [h, LinearMap.toMatrix'_id]

/-- Full-column embeddings can be aligned by an invertible matrix whose displacement
factors through their exact difference. Both inverse identities are supplied. -/
theorem exists_embedding_matrix_extension (X0 X1 : Matrix n m F)
    (h0 : Function.Injective X0.mulVec) (h1 : Function.Injective X1.mulVec) :
    ∃ (S Sinv : Matrix n n F) (D : Matrix m n F),
      S * Sinv = 1 ∧ Sinv * S = 1 ∧ S * X0 = X1 ∧ S - 1 = (X1 - X0) * D := by
  classical
  have hx0 : Function.Injective (Matrix.toLin' X0) := by
    rw [Matrix.toLin'_apply']
    exact h0
  have hx1 : Function.Injective (Matrix.toLin' X1) := by
    rw [Matrix.toLin'_apply']
    exact h1
  obtain ⟨S, D, hS, hD⟩ := exists_nearby_embedding_factor
    (Matrix.toLin' X0) (Matrix.toLin' X1) hx0 hx1
  refine ⟨LinearMap.toMatrix' S.toLinearMap, LinearMap.toMatrix' S.symm.toLinearMap,
    LinearMap.toMatrix' D, toMatrix_equiv_mul_symm S, toMatrix_equiv_mul_symm S.symm, ?_, ?_⟩
  · have hh := congrArg LinearMap.toMatrix' hS
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hh
  · have hh := congrArg LinearMap.toMatrix' hD
    simpa only [map_sub, LinearMap.toMatrix'_id, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] using hh

/-- Full-row maps can be aligned by an invertible matrix whose displacement factors
on the right through their exact difference. Both inverse identities are supplied. -/
theorem exists_surjection_matrix_extension (Y0 Y1 : Matrix p n F)
    (h0 : Function.Surjective Y0.mulVec) (h1 : Function.Surjective Y1.mulVec) :
    ∃ (T Tinv : Matrix n n F) (W : Matrix n p F),
      T * Tinv = 1 ∧ Tinv * T = 1 ∧ Y1 * T = Y0 ∧ T - 1 = W * (Y1 - Y0) := by
  classical
  have hy0 : Function.Surjective (Matrix.toLin' Y0) := by
    rw [Matrix.toLin'_apply']
    exact h0
  have hy1 : Function.Surjective (Matrix.toLin' Y1) := by
    rw [Matrix.toLin'_apply']
    exact h1
  obtain ⟨T, W, hT, hW⟩ := exists_nearby_surjection_factor
    (Matrix.toLin' Y0) (Matrix.toLin' Y1)
    (Matrix.toLin' Y1 - Matrix.toLin' Y0) hy0 hy1 le_rfl
  refine ⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap,
    LinearMap.toMatrix' W, toMatrix_equiv_mul_symm T, toMatrix_equiv_mul_symm T.symm, ?_, ?_⟩
  · have hh := congrArg LinearMap.toMatrix' hT
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hh
  · have hh := congrArg LinearMap.toMatrix' hW
    simpa only [map_sub, LinearMap.toMatrix'_id, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] using hh

end MatCP1Converse
