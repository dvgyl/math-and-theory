module

public import MatCP1Converse.ForwardCombinationMatrix
public import MatCP1Converse.ForwardPadding
public import MatCP1Converse.ForwardDilationPencil
public import MatCP1Converse.PencilMixedFactors

@[expose] public section

namespace MatCP1Converse

set_option maxHeartbeats 1000000

variable {F m n x : Type*} [Field F] [Infinite F]
  [Fintype m] [Fintype n] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq x]

/-- An actual normal-rank bound on the difference of arbitrary pencils gives
the prescribed scalar completion of their literal three-block dilations. The
mixed factorization is proved from that normal rank, and padding is constructed. -/
theorem matrix_dilation_completion_of_rank_bound
    (A0 A1 B0 B1 : Matrix m n F) (c d : F)
    (hRank : Pencil.normalRank ((A0 - B0, A1 - B1) : Pencil F m n) ≤ Fintype.card x) :
    MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
      (fun j : Bool => Matrix.fromBlocks (matrixDilationFamily B0 B1 c d j) 0 0
        (if j then (1 : Matrix x x F) else -d • (1 : Matrix x x F))) := by
  let D : Pencil F m n := (A0 - B0, A1 - B1)
  obtain ⟨a, b, U, Z, R0, R1, L0, L1, hab, h0, h1⟩ :=
    Pencil.exists_rank_mixed_factorization D
  have hmix := matrix_dilation_same_anchor A0 A1 B0 B1 U R0 R1 L0 L1 Z h0 h1 c d
  have hcard : Fintype.card (Fin a) + Fintype.card (Fin b) ≤ Fintype.card x := by
    simpa only [Fintype.card_fin, hab] using hRank
  exact matrixJointCompression_trans hmix
    (matrix_scalar_sum_padding (a := Fin a) (b := Fin b) (x := x)
      (matrixDilationFamily B0 B1 c d) d hcard)

/-- The complete raw-dilation forward implication from the actual minimum
over both constant strict-equivalence classes. No chosen representative,
rank-factorization, intermediate-spectrum, or barred-pencil hypothesis is
assumed. Every compression witness is constant over the original field. -/
theorem matrix_dilation_completion_forward
    (A0 A1 B0 B1 : Matrix m n F) (c d : F)
    (h : Pencil.orbitDistance (A0, A1) (B0, B1) ≤ Fintype.card x) :
    MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
      (fun j : Bool => Matrix.fromBlocks (matrixDilationFamily B0 B1 c d j) 0 0
        (if j then (1 : Matrix x x F) else -d • (1 : Matrix x x F))) := by
  obtain ⟨A', B', hA, hB, hRank⟩ :=
    (Pencil.orbitDistance_le_iff (A0, A1) (B0, B1) (Fintype.card x)).mp h
  have hmiddle := matrix_dilation_completion_of_rank_bound A'.1 A'.2 B'.1 B'.2 c d hRank
  have hleft : MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
      (matrixDilationFamily A'.1 A'.2 c d) :=
    (familyStrictEquivalence_iff_matrixCompression _ _).mp
      (Pencil.dilate_family_strictEquivalence c d (Pencil.strictEquivalent_symm hA))
  have hright0 : MatCP1.MatrixJointCompression (matrixDilationFamily B'.1 B'.2 c d)
      (matrixDilationFamily B0 B1 c d) :=
    (familyStrictEquivalence_iff_matrixCompression _ _).mp
      (Pencil.dilate_family_strictEquivalence c d hB)
  have hright := matrixJointCompression_prodMap _ _
    (fun j : Bool => if j then (1 : Matrix x x F) else -d • (1 : Matrix x x F)) hright0
  exact matrixJointCompression_trans hleft (matrixJointCompression_trans hmiddle hright)

end MatCP1Converse
