module

public import MatCP1Converse.ForwardDilation
public import MatCP1.MatrixCompression
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

namespace MatCP1Converse

variable {F m n a b : Type*} [Field F]

/-- Sum coordinates for the three-block source or target of the dilation. -/
def dilationSumCoordinate (i j : Type*) :
    ((i ⊕ (i ⊕ j)) → F) ≃ₗ[F] ((i → F) × ((i → F) × (j → F))) :=
  (LinearEquiv.sumArrowLequivProdArrow i (i ⊕ j) F F).trans
    ((LinearEquiv.refl F (i → F)).prodCongr
      (LinearEquiv.sumArrowLequivProdArrow i j F F))

variable [Fintype m] [Fintype n] [Fintype a] [Fintype b]
  [DecidableEq m] [DecidableEq n] [DecidableEq a] [DecidableEq b]

/-- Literal constant coefficient of `K_{c,d}(A)`. -/
def matrixDilationConstant (A : Matrix m n F) (c d : F) :
    Matrix (m ⊕ (m ⊕ n)) (n ⊕ (n ⊕ m)) F :=
  Matrix.fromBlocks A (Matrix.fromCols 0 1) (Matrix.fromRows 0 1)
    (Matrix.fromBlocks 0 (c • 1) (d • 1) 0)

/-- Literal linear coefficient of `K_{c,d}(A)`. -/
def matrixDilationLinear (A : Matrix m n F) :
    Matrix (m ⊕ (m ⊕ n)) (n ⊕ (n ⊕ m)) F :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks 0 (-1) (-1) 0)

def matrixDilationFamily (A0 A1 : Matrix m n F) (c d : F) :
    Bool → Matrix (m ⊕ (m ⊕ n)) (n ⊕ (n ⊕ m)) F :=
  fun i => if i then matrixDilationLinear A1 else matrixDilationConstant A0 c d

theorem matrixDilationConstant_conj (A : Matrix m n F) (c d : F) :
    (dilationSumCoordinate (F := F) m n).toLinearMap.comp
      ((Matrix.toLin' (matrixDilationConstant A c d)).comp
        (dilationSumCoordinate (F := F) n m).symm.toLinearMap) =
      dilationConstant (Matrix.toLin' A) c d := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  apply Prod.ext
  · funext i
    simp [dilationSumCoordinate, matrixDilationConstant, Matrix.toLin'_apply,
      Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec, Matrix.fromRows_mulVec,
      LinearEquiv.sumArrowLequivProdArrow]
    rfl
  · apply Prod.ext
    · funext i
      simp [dilationSumCoordinate, matrixDilationConstant, Matrix.toLin'_apply,
        Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec, Matrix.fromRows_mulVec,
        Matrix.smul_mulVec, LinearEquiv.sumArrowLequivProdArrow]
    · funext i
      simp [dilationSumCoordinate, matrixDilationConstant, Matrix.toLin'_apply,
        Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec, Matrix.fromRows_mulVec,
        Matrix.smul_mulVec, LinearEquiv.sumArrowLequivProdArrow]

theorem matrixDilationLinear_conj (A : Matrix m n F) :
    (dilationSumCoordinate (F := F) m n).toLinearMap.comp
      ((Matrix.toLin' (matrixDilationLinear A)).comp
        (dilationSumCoordinate (F := F) n m).symm.toLinearMap) =
      dilationLinear (Matrix.toLin' A) := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  apply Prod.ext
  · funext i
    simp [dilationSumCoordinate, matrixDilationLinear, Matrix.toLin'_apply,
      Matrix.fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow]
    rfl
  · apply Prod.ext
    · funext i
      simp [dilationSumCoordinate, matrixDilationLinear, Matrix.toLin'_apply,
        Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, LinearEquiv.sumArrowLequivProdArrow]
    · funext i
      simp [dilationSumCoordinate, matrixDilationLinear, Matrix.toLin'_apply,
        Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, LinearEquiv.sumArrowLequivProdArrow]

theorem matrixDilationFamily_conj (A0 A1 : Matrix m n F) (c d : F) (i : Bool) :
    (dilationSumCoordinate (F := F) m n).toLinearMap.comp
      ((Matrix.toLin' (matrixDilationFamily A0 A1 c d i)).comp
        (dilationSumCoordinate (F := F) n m).symm.toLinearMap) =
      dilationFamily (Matrix.toLin' A0) (Matrix.toLin' A1) c d i := by
  cases i
  · exact matrixDilationConstant_conj A0 c d
  · exact matrixDilationLinear_conj A1

def scalarMatrixDilationFamily (d : F) : Bool → Matrix a a F :=
  fun i => if i then 1 else -d • 1

theorem scalarMatrixDilationFamily_toLin (d : F) (i : Bool) :
    Matrix.toLin' (scalarMatrixDilationFamily (a := a) d i) =
      scalarDilationFamily (E := a → F) d i := by
  cases i <;> simp [scalarMatrixDilationFamily, scalarDilationFamily, neg_smul]
  exact (neg_smul d (LinearMap.id : (a → F) →ₗ[F] (a → F))).symm

section ExtendedCoordinates

variable {V W : Type*} [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Coordinates for a matrix space followed by two separate added blocks. -/
def twoBorderSumCoordinate (i j k : Type*) (e : (i → F) ≃ₗ[F] V) :
    (((i ⊕ j) ⊕ k) → F) ≃ₗ[F] ((V × (j → F)) × (k → F)) :=
  (LinearEquiv.sumArrowLequivProdArrow (i ⊕ j) k F F).trans
    (((LinearEquiv.sumArrowLequivProdArrow i j F F).trans
      (e.prodCongr (LinearEquiv.refl F (j → F)))).prodCongr
        (LinearEquiv.refl F (k → F)))

omit [Fintype m] [DecidableEq m] in
theorem twoBorder_matrix_conj (A : Matrix m n F) (S : Matrix a a F) (T : Matrix b b F)
    (em : (m → F) ≃ₗ[F] W) (en : (n → F) ≃ₗ[F] V) :
    (twoBorderSumCoordinate m a b em).toLinearMap.comp
      ((Matrix.toLin' (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 S) 0 0 T)).comp
        (twoBorderSumCoordinate n a b en).symm.toLinearMap) =
      ((em.toLinearMap.comp ((Matrix.toLin' A).comp en.symm.toLinearMap)).prodMap
        (Matrix.toLin' S)).prodMap (Matrix.toLin' T) := by
  apply LinearMap.ext
  rintro ⟨⟨v, x⟩, y⟩
  simp [twoBorderSumCoordinate, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
    LinearEquiv.sumArrowLequivProdArrow]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

end ExtendedCoordinates

theorem matrixDilationFamily_unconj (A0 A1 : Matrix m n F) (c d : F) (i : Bool) :
    (dilationSumCoordinate (F := F) m n).symm.toLinearMap.comp
      ((dilationFamily (Matrix.toLin' A0) (Matrix.toLin' A1) c d i).comp
        (dilationSumCoordinate (F := F) n m).toLinearMap) =
      Matrix.toLin' (matrixDilationFamily A0 A1 c d i) := by
  rw [← matrixDilationFamily_conj]
  apply LinearMap.ext
  intro v
  simp

/-- The actual literal-matrix forward embedding for a mixed factorization of
both perturbation coefficients. The output compression maps are constant and
have full row and column rank. All dimensions may be empty. -/
theorem matrix_dilation_compression_of_factorized_difference
    (B0 B1 C0 C1 : Matrix m n F) (U : Matrix m a F)
    (R0 R1 : Matrix a n F) (L0 L1 : Matrix m b F) (Z : Matrix b n F)
    (h0 : B0 - C0 = U * R0 + L0 * Z)
    (h1 : B1 - C1 = U * R1 + L1 * Z) (c d : F) :
    MatCP1.MatrixJointCompression (matrixDilationFamily B0 B1 c d)
      (fun i => Matrix.fromBlocks
        (Matrix.fromBlocks (matrixDilationFamily C0 C1 c d i) 0 0
          (scalarMatrixDilationFamily (a := a) d i)) 0 0
        (scalarMatrixDilationFamily (a := b) c i)) := by
  have hl0 : Matrix.toLin' B0 - Matrix.toLin' C0 =
      (Matrix.toLin' U).comp (Matrix.toLin' R0) +
        (Matrix.toLin' L0).comp (Matrix.toLin' Z) := by
    simpa only [map_sub, map_add, Matrix.toLin'_mul] using congrArg Matrix.toLin' h0
  have hl1 : Matrix.toLin' B1 - Matrix.toLin' C1 =
      (Matrix.toLin' U).comp (Matrix.toLin' R1) +
        (Matrix.toLin' L1).comp (Matrix.toLin' Z) := by
    simpa only [map_sub, map_add, Matrix.toLin'_mul] using congrArg Matrix.toLin' h1
  have h := jointCompression_dilation_of_factorized_difference
    (Matrix.toLin' B0) (Matrix.toLin' B1) (Matrix.toLin' C0) (Matrix.toLin' C1)
    (Matrix.toLin' U) (Matrix.toLin' R0) (Matrix.toLin' R1)
    (Matrix.toLin' L0) (Matrix.toLin' L1) (Matrix.toLin' Z) hl0 hl1 c d
  let em := dilationSumCoordinate (F := F) m n
  let en := dilationSumCoordinate (F := F) n m
  let ebm := twoBorderSumCoordinate (m ⊕ (m ⊕ n)) a b em
  let ebn := twoBorderSumCoordinate (n ⊕ (n ⊕ m)) a b en
  have hbig (i : Bool) :
      ebm.symm.toLinearMap.comp
        ((((dilationFamily (Matrix.toLin' C0) (Matrix.toLin' C1) c d i).prodMap
          (scalarDilationFamily (E := a → F) d i)).prodMap
          (scalarDilationFamily (E := b → F) c i)).comp ebn.toLinearMap) =
      Matrix.toLin' (Matrix.fromBlocks
        (Matrix.fromBlocks (matrixDilationFamily C0 C1 c d i) 0 0
          (scalarMatrixDilationFamily (a := a) d i)) 0 0
        (scalarMatrixDilationFamily (a := b) c i)) := by
    have hb := twoBorder_matrix_conj (matrixDilationFamily C0 C1 c d i)
      (scalarMatrixDilationFamily (a := a) d i)
      (scalarMatrixDilationFamily (a := b) c i) em en
    change ebm.toLinearMap.comp ((Matrix.toLin' _).comp ebn.symm.toLinearMap) = _ at hb
    dsimp only [em, en] at hb
    rw [matrixDilationFamily_conj, scalarMatrixDilationFamily_toLin,
      scalarMatrixDilationFamily_toLin] at hb
    rw [← hb]
    apply LinearMap.ext
    intro v
    simp
  have h' := MatCP1.JointCompression.linearEquiv _ _ en.symm em.symm ebn.symm ebm.symm h
  apply (MatCP1.matrixJointCompression_iff_linear _ _).mpr
  change MatCP1.JointCompression
    (fun i => Matrix.toLin' (matrixDilationFamily B0 B1 c d i))
    (fun i => Matrix.toLin' (Matrix.fromBlocks
      (Matrix.fromBlocks (matrixDilationFamily C0 C1 c d i) 0 0
        (scalarMatrixDilationFamily (a := a) d i)) 0 0
      (scalarMatrixDilationFamily (a := b) c i)))
  convert h' using 1
  · funext i
    exact (matrixDilationFamily_unconj B0 B1 c d i).symm
  · funext i
    exact (hbig i).symm

end MatCP1Converse
