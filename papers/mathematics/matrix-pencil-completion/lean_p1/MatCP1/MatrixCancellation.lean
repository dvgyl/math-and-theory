module

public import MatCP1.Cancellation
public import MatCP1.MatrixCompression

@[expose] public section

namespace MatCP1

variable {F I m n p q u v : Type*} [Field F] [Infinite F]
  [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [Fintype u] [Fintype v]

/-- A common rectangular block summand cancels from simultaneous full-row/full-column
matrix compression. No finiteness assumption is placed on the family index `I`. -/
theorem matrixJointCompression_common_summand_iff
    (A : I → Matrix m n F) (B : I → Matrix p q F) (S : I → Matrix u v F) :
    MatrixJointCompression (fun i => Matrix.fromBlocks (A i) 0 0 (S i))
      (fun i => Matrix.fromBlocks (B i) 0 0 (S i)) ↔
    MatrixJointCompression A B := by
  rw [matrixJointCompression_blocks_iff_linear, matrixJointCompression_iff_linear]
  exact jointCompression_common_summand_iff
    (fun i => (A i).mulVecLin) (fun i => (B i).mulVecLin) (fun i => (S i).mulVecLin)

/-- The cancellation theorem with every matrix and full-rank hypothesis exposed.
Surjectivity of `P.mulVec` means full row rank, and injectivity of `Q.mulVec` means full
column rank. All six finite index types may be empty and the field may have any characteristic. -/
theorem matrix_common_summand_cancellation
    (A : I → Matrix m n F) (B : I → Matrix p q F) (S : I → Matrix u v F)
    (P : Matrix (m ⊕ u) (p ⊕ u) F) (Q : Matrix (q ⊕ v) (n ⊕ v) F)
    (hP : Function.Surjective P.mulVec) (hQ : Function.Injective Q.mulVec)
    (hPQ : ∀ i, P * Matrix.fromBlocks (B i) 0 0 (S i) * Q =
      Matrix.fromBlocks (A i) 0 0 (S i)) :
    ∃ (P' : Matrix m p F) (Q' : Matrix q n F),
      Function.Surjective P'.mulVec ∧ Function.Injective Q'.mulVec ∧
        ∀ i, P' * B i * Q' = A i :=
  (matrixJointCompression_common_summand_iff A B S).mp ⟨P, Q, hP, hQ, hPQ⟩

end MatCP1
