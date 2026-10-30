module

public import MatCP1.Compression
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Block

@[expose] public section

namespace MatCP1

variable {F I m n p q u v : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [Fintype u] [Fintype v]

/-- Rectangular matrix compression by a single full-row matrix and a single full-column
matrix, simultaneously for every member of the family. Full rank is expressed by the
equivalent surjectivity/injectivity conditions on multiplication by a column vector. -/
def MatrixJointCompression (A : I → Matrix m n F) (B : I → Matrix p q F) : Prop :=
  ∃ (P : Matrix m p F) (Q : Matrix q n F),
    Function.Surjective P.mulVec ∧ Function.Injective Q.mulVec ∧
      ∀ i, P * B i * Q = A i

omit [Fintype m] in
/-- The matrix statement is exactly the linear-map statement in standard coordinates. -/
theorem matrixJointCompression_iff_linear
    (A : I → Matrix m n F) (B : I → Matrix p q F) :
    MatrixJointCompression A B ↔
      JointCompression (fun i => (A i).mulVecLin) (fun i => (B i).mulVecLin) := by
  classical
  constructor
  · rintro ⟨P, Q, hP, hQ, hPQ⟩
    refine ⟨P.mulVecLin, Q.mulVecLin, hP, hQ, ?_⟩
    intro i
    have hi := congrArg Matrix.mulVecLin (hPQ i)
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_assoc] using hi
  · rintro ⟨P, Q, hP, hQ, hPQ⟩
    refine ⟨LinearMap.toMatrix' P, LinearMap.toMatrix' Q, ?_, ?_, ?_⟩
    · intro a
      obtain ⟨b, hb⟩ := hP a
      exact ⟨b, by simpa only [LinearMap.toMatrix'_mulVec] using hb⟩
    · intro x y hxy
      apply hQ
      simpa only [LinearMap.toMatrix'_mulVec] using hxy
    · intro i
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
        Matrix.toLin'_toMatrix']
      simpa only [Matrix.toLin'_apply', LinearMap.comp_assoc] using hPQ i

omit [Fintype m] [Fintype u] in
/-- Standard block diagonal matrices act as the product of their two linear maps. -/
theorem block_mulVecLin_conj (A : Matrix m n F) (S : Matrix u v F) :
    (LinearEquiv.sumArrowLequivProdArrow m u F F).toLinearMap.comp
      ((Matrix.fromBlocks A 0 0 S).mulVecLin.comp
        (LinearEquiv.sumArrowLequivProdArrow n v F F).symm.toLinearMap) =
      A.mulVecLin.prodMap S.mulVecLin := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext i
    simp [Matrix.fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow]
    rfl
  · funext j
    simp [Matrix.fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow]
    rfl

omit [Fintype m] [Fintype u] in
/-- The inverse coordinate change recovers the literal block matrix, including empty
row or column index types. -/
theorem prod_mulVecLin_conj (A : Matrix m n F) (S : Matrix u v F) :
    (LinearEquiv.sumArrowLequivProdArrow m u F F).symm.toLinearMap.comp
      ((A.mulVecLin.prodMap S.mulVecLin).comp
        (LinearEquiv.sumArrowLequivProdArrow n v F F).toLinearMap) =
      (Matrix.fromBlocks A 0 0 S).mulVecLin := by
  rw [← block_mulVecLin_conj A S]
  ext x i
  simp

omit [Fintype m] in
/-- Literal matrix block sums and product-space compression have identical content. -/
theorem matrixJointCompression_blocks_iff_linear
    (A : I → Matrix m n F) (B : I → Matrix p q F) (S : I → Matrix u v F) :
    MatrixJointCompression (fun i => Matrix.fromBlocks (A i) 0 0 (S i))
      (fun i => Matrix.fromBlocks (B i) 0 0 (S i)) ↔
    JointCompression (fun i => (A i).mulVecLin.prodMap (S i).mulVecLin)
      (fun i => (B i).mulVecLin.prodMap (S i).mulVecLin) := by
  rw [matrixJointCompression_iff_linear]
  constructor
  · intro h
    have h' := JointCompression.linearEquiv _ _
      (LinearEquiv.sumArrowLequivProdArrow n v F F)
      (LinearEquiv.sumArrowLequivProdArrow m u F F)
      (LinearEquiv.sumArrowLequivProdArrow q v F F)
      (LinearEquiv.sumArrowLequivProdArrow p u F F) h
    simpa only [block_mulVecLin_conj] using h'
  · intro h
    have h' := JointCompression.linearEquiv _ _
      (LinearEquiv.sumArrowLequivProdArrow n v F F).symm
      (LinearEquiv.sumArrowLequivProdArrow m u F F).symm
      (LinearEquiv.sumArrowLequivProdArrow q v F F).symm
      (LinearEquiv.sumArrowLequivProdArrow p u F F).symm h
    simpa only [LinearEquiv.symm_symm, prod_mulVecLin_conj] using h'

end MatCP1
