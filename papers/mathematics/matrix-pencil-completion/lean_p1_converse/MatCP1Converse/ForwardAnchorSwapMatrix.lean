module

public import MatCP1Converse.ForwardAnchorSwap
public import MatCP1Converse.ForwardDilationMatrix
public import MatCP1Converse.StrictCancellation

@[expose] public section

namespace MatCP1Converse

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Literal constant strict equivalence interchanging the two anchors of `K`.
It holds for every pencil over every field, without assumptions at either anchor. -/
theorem matrix_dilation_anchor_swap (A0 A1 : Matrix m n F) (c d : F) :
    FamilyStrictEquivalence (matrixDilationFamily A0 A1 d c)
      (matrixDilationFamily A0 A1 c d) := by
  have h := jointCompression_dilation_anchor_swap (Matrix.toLin' A0) (Matrix.toLin' A1) c d
  have h' := MatCP1.JointCompression.linearEquiv _ _
    (dilationSumCoordinate (F := F) n m).symm
    (dilationSumCoordinate (F := F) m n).symm
    (dilationSumCoordinate (F := F) n m).symm
    (dilationSumCoordinate (F := F) m n).symm h
  apply (familyStrictEquivalence_iff_matrixCompression _ _).mpr
  apply (MatCP1.matrixJointCompression_iff_linear _ _).mpr
  simp only [LinearEquiv.symm_symm, matrixDilationFamily_unconj] at h'
  simpa only [Matrix.toLin'_apply'] using h'

end MatCP1Converse
