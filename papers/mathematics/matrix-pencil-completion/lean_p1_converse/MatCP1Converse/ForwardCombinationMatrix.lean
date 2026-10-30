module

public import MatCP1Converse.ForwardCombination
public import MatCP1Converse.ForwardDilationMatrix

@[expose] public section

namespace MatCP1Converse

section Stabilize

variable {F I m n p q u v : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype u] [Fintype v]

omit [Fintype m] in
theorem matrixJointCompression_prodMap
    (A : I → Matrix m n F) (B : I → Matrix p q F) (S : I → Matrix u v F)
    (h : MatCP1.MatrixJointCompression A B) :
    MatCP1.MatrixJointCompression (fun i => Matrix.fromBlocks (A i) 0 0 (S i))
      (fun i => Matrix.fromBlocks (B i) 0 0 (S i)) := by
  apply (MatCP1.matrixJointCompression_blocks_iff_linear _ _ _).mpr
  exact MatCP1.JointCompression.prodMap _ _ _
    ((MatCP1.matrixJointCompression_iff_linear _ _).mp h)

end Stabilize

section Dilation

variable {F m n a b : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype a] [Fintype b]
  [DecidableEq m] [DecidableEq n] [DecidableEq a] [DecidableEq b]

/-- Literal-matrix mixed-factor forward completion with every added scalar
at the same prescribed anchor. The intermediate pencil and its spectra do not
appear as hypotheses. -/
theorem matrix_dilation_same_anchor
    (A0 A1 B0 B1 : Matrix m n F) (U : Matrix m a F)
    (R0 R1 : Matrix a n F) (L0 L1 : Matrix m b F) (Z : Matrix b n F)
    (h0 : A0 - B0 = U * R0 + L0 * Z)
    (h1 : A1 - B1 = U * R1 + L1 * Z) (c d : F) :
    MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
      (fun i => Matrix.fromBlocks
        (Matrix.fromBlocks (matrixDilationFamily B0 B1 c d i) 0 0
          (scalarMatrixDilationFamily (a := a) d i)) 0 0
        (scalarMatrixDilationFamily (a := b) d i)) := by
  have hl0 : Matrix.toLin' A0 - Matrix.toLin' B0 =
      (Matrix.toLin' U).comp (Matrix.toLin' R0) +
        (Matrix.toLin' L0).comp (Matrix.toLin' Z) := by
    simpa only [map_sub, map_add, Matrix.toLin'_mul] using congrArg Matrix.toLin' h0
  have hl1 : Matrix.toLin' A1 - Matrix.toLin' B1 =
      (Matrix.toLin' U).comp (Matrix.toLin' R1) +
        (Matrix.toLin' L1).comp (Matrix.toLin' Z) := by
    simpa only [map_sub, map_add, Matrix.toLin'_mul] using congrArg Matrix.toLin' h1
  have h := jointCompression_dilation_same_anchor
    (Matrix.toLin' A0) (Matrix.toLin' A1) (Matrix.toLin' B0) (Matrix.toLin' B1)
    (Matrix.toLin' U) (Matrix.toLin' R0) (Matrix.toLin' R1)
    (Matrix.toLin' L0) (Matrix.toLin' L1) (Matrix.toLin' Z) hl0 hl1 c d
  let em := dilationSumCoordinate (F := F) m n
  let en := dilationSumCoordinate (F := F) n m
  let ebm := twoBorderSumCoordinate (m ⊕ (m ⊕ n)) a b em
  let ebn := twoBorderSumCoordinate (n ⊕ (n ⊕ m)) a b en
  have hbig (i : Bool) :
      ebm.symm.toLinearMap.comp
        ((((dilationFamily (Matrix.toLin' B0) (Matrix.toLin' B1) c d i).prodMap
          (scalarDilationFamily (E := a → F) d i)).prodMap
          (scalarDilationFamily (E := b → F) d i)).comp ebn.toLinearMap) =
      Matrix.toLin' (Matrix.fromBlocks
        (Matrix.fromBlocks (matrixDilationFamily B0 B1 c d i) 0 0
          (scalarMatrixDilationFamily (a := a) d i)) 0 0
        (scalarMatrixDilationFamily (a := b) d i)) := by
    have hb := twoBorder_matrix_conj (matrixDilationFamily B0 B1 c d i)
      (scalarMatrixDilationFamily (a := a) d i)
      (scalarMatrixDilationFamily (a := b) d i) em en
    change ebm.toLinearMap.comp ((Matrix.toLin' _).comp ebn.symm.toLinearMap) = _ at hb
    dsimp only [em, en] at hb
    rw [matrixDilationFamily_conj, scalarMatrixDilationFamily_toLin,
      scalarMatrixDilationFamily_toLin] at hb
    rw [← hb]
    apply LinearMap.ext
    intro z
    simp
  have h' := MatCP1.JointCompression.linearEquiv _ _ en.symm em.symm ebn.symm ebm.symm h
  apply (MatCP1.matrixJointCompression_iff_linear _ _).mpr
  change MatCP1.JointCompression
    (fun i => Matrix.toLin' (matrixDilationFamily A0 A1 c d i))
    (fun i => Matrix.toLin' (Matrix.fromBlocks
      (Matrix.fromBlocks (matrixDilationFamily B0 B1 c d i) 0 0
        (scalarMatrixDilationFamily (a := a) d i)) 0 0
      (scalarMatrixDilationFamily (a := b) d i)))
  convert h' using 1
  · funext i
    exact (matrixDilationFamily_unconj A0 A1 c d i).symm
  · funext i
    exact (hbig i).symm

end Dilation

end MatCP1Converse
