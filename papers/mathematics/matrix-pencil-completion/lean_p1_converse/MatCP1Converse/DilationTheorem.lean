module

public import MatCP1Converse.RawDilationForward
public import MatCP1Converse.RawDilationConverse

@[expose] public section

namespace MatCP1Converse

open Matrix

set_option maxHeartbeats 1000000

variable {F m n x : Type*} [Field F] [Infinite F]
  [Fintype m] [Fintype n] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq x]

/-- Exact equivalence between orbit normal-rank distance and the prescribed
scalar completion of the explicit dilations. The anchors may be spectral
points; their distinctness is the only condition on them. -/
theorem matrix_dilation_completion_iff
    (A0 A1 B0 B1 : Matrix m n F) (c d : F) (hcd : c ≠ d) :
    Pencil.orbitDistance (A0, A1) (B0, B1) ≤ Fintype.card x ↔
      MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
        (fun j : Bool => fromBlocks (matrixDilationFamily B0 B1 c d j) 0 0
          (if j then (1 : Matrix x x F) else -d • (1 : Matrix x x F))) :=
  ⟨matrix_dilation_completion_forward A0 A1 B0 B1 c d,
    matrix_dilation_completion_converse A0 A1 B0 B1 c d hcd⟩

omit [Fintype x] [DecidableEq x] in
/-- Natural-number border size, including zero. All original row and column
index types may also be empty. -/
theorem matrix_dilation_completion_iff_nat
    (A0 A1 B0 B1 : Matrix m n F) (c d : F) (hcd : c ≠ d) (k : ℕ) :
    Pencil.orbitDistance (A0, A1) (B0, B1) ≤ k ↔
      MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
        (fun j : Bool => fromBlocks (matrixDilationFamily B0 B1 c d j) 0 0
          (if j then (1 : Matrix (Fin k) (Fin k) F)
            else -d • (1 : Matrix (Fin k) (Fin k) F))) := by
  simpa only [Fintype.card_fin] using
    (matrix_dilation_completion_iff (x := Fin k) A0 A1 B0 B1 c d hcd)

omit [Fintype x] [DecidableEq x] in
/-- The complete theorem with the original constant full-row/full-column
matrices and both coefficient equations exposed. No canonical form,
presentation, rank factorization or favorable chart is assumed. -/
theorem dilation_rank_distance_iff
    (A0 A1 B0 B1 : Matrix m n F) (c d : F) (hcd : c ≠ d) (k : ℕ) :
    Pencil.orbitDistance (A0, A1) (B0, B1) ≤ k ↔
      ∃ (P : Matrix (m ⊕ (m ⊕ n)) ((m ⊕ (m ⊕ n)) ⊕ Fin k) F)
        (Q : Matrix ((n ⊕ (n ⊕ m)) ⊕ Fin k) (n ⊕ (n ⊕ m)) F),
        Function.Surjective P.mulVec ∧ Function.Injective Q.mulVec ∧
        P * fromBlocks (matrixDilationConstant B0 c d) 0 0
          (-d • (1 : Matrix (Fin k) (Fin k) F)) * Q = matrixDilationConstant A0 c d ∧
        P * fromBlocks (matrixDilationLinear B1) 0 0
          (1 : Matrix (Fin k) (Fin k) F) * Q = matrixDilationLinear A1 := by
  rw [matrix_dilation_completion_iff_nat A0 A1 B0 B1 c d hcd k]
  constructor
  · rintro ⟨P, Q, hP, hQ, hPQ⟩
    refine ⟨P, Q, hP, hQ, ?_, ?_⟩
    · simpa only [matrixDilationFamily, Bool.false_eq_true, ↓reduceIte] using hPQ false
    · simpa only [matrixDilationFamily, ↓reduceIte] using hPQ true
  · rintro ⟨P, Q, hP, hQ, h0, h1⟩
    refine ⟨P, Q, hP, hQ, ?_⟩
    intro j
    cases j
    · simpa only [matrixDilationFamily, Bool.false_eq_true, ↓reduceIte] using h0
    · simpa only [matrixDilationFamily, ↓reduceIte] using h1

end MatCP1Converse
