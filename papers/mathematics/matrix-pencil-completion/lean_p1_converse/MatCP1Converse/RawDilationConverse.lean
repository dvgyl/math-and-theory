module

public import MatCP1Converse.ComplementReindex
public import MatCP1Converse.CompletionSubpencil
public import MatCP1Converse.ForwardDilationRecoveryMatrix

@[expose] public section

namespace MatCP1Converse

open Matrix

section Rank

variable {F o i : Type*} [Field F] [Fintype o] [Fintype i]
  [DecidableEq o] [DecidableEq i]

theorem raw_dilation_rank_transport
    (M : Matrix o i F) (P Pi : Matrix o o F) (Q Qi : Matrix i i F)
    (hPiP : Pi * P = 1) (hQQi : Q * Qi = 1) :
    (P * M * Q).rank = M.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hrec : Pi * (P * M * Q) * Qi = M := by
      simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    calc
      M.rank = (Pi * (P * M * Q) * Qi).rank := congrArg Matrix.rank hrec.symm
      _ ≤ (P * M * Q).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem raw_dilation_rank_smul_le (t : F) (M : Matrix o i F) :
    (t • M).rank ≤ M.rank := by
  have hfac : t • M = (t • (1 : Matrix o o F)) * M := by
    simp only [Matrix.smul_mul, Matrix.one_mul]
  rw [hfac]
  exact Matrix.rank_mul_le_right _ _

end Rank

section Converse

variable {F m n x : Type*} [Field F] [Infinite F]
  [Fintype m] [Fintype n] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq x]

/-- A scalar completion of the explicit three-block dilations forces the
original pencils to be within the same actual normal-rank bound.

This theorem is unconditional apart from its literal matrix-compression
premise and `c ≠ d`. The intrinsic presentations, anchor ranks, common-kernel
conditions, fixed-factor correction and complementary contraction are all
constructed and verified internally. No Kronecker decomposition, barred-pencil
identification, or extra presentation hypothesis occurs in the statement. -/
theorem matrix_dilation_completion_converse
    (A0 A1 B0 B1 : Matrix m n F) (c d : F) (hcd : c ≠ d)
    (h : MatCP1.MatrixJointCompression (matrixDilationFamily A0 A1 c d)
      (fun j : Bool => fromBlocks (matrixDilationFamily B0 B1 c d j) 0 0
        (if j then (1 : Matrix x x F) else -d • (1 : Matrix x x F)))) :
    Pencil.orbitDistance (A0, A1) (B0, B1) ≤ Fintype.card x := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h
  have hcoef0 : P * fromBlocks (matrixDilationConstant B0 c d) 0 0
      (-d • (1 : Matrix x x F)) * Q = matrixDilationConstant A0 c d := by
    simpa [matrixDilationFamily] using hPQ false
  have hcoef1 : P * fromBlocks (matrixDilationLinear B1) 0 0
      (1 : Matrix x x F) * Q = matrixDilationLinear A1 := by
    simpa [matrixDilationFamily] using hPQ true
  have hanchor : (matrixDilationConstant A0 c d + d • matrixDilationLinear A1).rank =
      (matrixDilationConstant B0 c d + d • matrixDilationLinear B1).rank := by
    exact (matrix_dilation_rank_at_d A0 A1 c d).trans
      (matrix_dilation_rank_at_d B0 B1 c d).symm
  obtain ⟨D, p, pi, q, qi, hD, hppi, hpip, hqqi, hqiq, _, _, heval⟩ :=
    matrix_subpencil_extract_fixed_factor d
      (matrixDilationConstant A0 c d) (matrixDilationLinear A1)
      (matrixDilationConstant B0 c d) (matrixDilationLinear B1)
      P Q hP hQ hcoef0 hcoef1 hanchor
  let E := matrixDilationEval A0 A1 c d d
  let H1 := matrixDilationEval A0 A1 c d c
  let H0 := p * matrixDilationEval B0 B1 c d c * q
  let C0 : Pencil F m n := (B0 + d • B1, B0 + c • B1)
  let C1 : Pencil F m n := (A0 + d • A1, A0 + c • A1)
  have hcommon : p * matrixDilationEval B0 B1 c d d * q = E := by
    simpa only [E, matrixDilationEval, sub_self, zero_smul, sub_zero] using (heval d).symm
  have hdiff : H1 - H0 = (c - d) • D := by
    have hc : H1 - (c - d) • D = H0 := heval c
    rw [← hc]
    abel
  have hErank : E.rank = Fintype.card (n ⊕ m) := matrix_dilation_rank_at_d A0 A1 c d
  have hH1rank : H1.rank = Fintype.card (n ⊕ m) := matrix_dilation_rank_at_c A0 A1 c d
  have hH0rank : H0.rank = Fintype.card (n ⊕ m) :=
    (raw_dilation_rank_transport (matrixDilationEval B0 B1 c d c) p pi q qi hpip hqqi).trans
      (matrix_dilation_rank_at_c B0 B1 c d)
  have hj1 : Function.Injective (fromRows E H1).mulVec :=
    matrix_dilation_joint_injective A0 A1 c d hcd
  have hs1 : Function.Surjective (fromCols E H1).mulVec :=
    matrix_dilation_joint_surjective A0 A1 c d hcd
  have hj0 : Function.Injective (fromRows E H0).mulVec := by
    have hh := complement_joint_injective_transport
      (matrixDilationEval B0 B1 c d d) (matrixDilationEval B0 B1 c d c)
      p pi q qi hpip hqiq (matrix_dilation_joint_injective B0 B1 c d hcd)
    simpa only [hcommon] using hh
  have hs0 : Function.Surjective (fromCols E H0).mulVec := by
    have hh := complement_joint_surjective_transport
      (matrixDilationEval B0 B1 c d d) (matrixDilationEval B0 B1 c d c)
      p pi q qi hppi hqqi (matrix_dilation_joint_surjective B0 B1 c d hcd)
    simpa only [hcommon] using hh
  have w1 : ComplementPresentation (n ⊕ m) (n ⊕ m) E H1 C1 :=
    matrix_dilation_complement_presentation A0 A1 c d hcd
  have w0 : ComplementPresentation (n ⊕ m) (n ⊕ m) E H0 C0 := by
    have ww := (matrix_dilation_complement_presentation B0 B1 c d hcd).ambient
      p pi q qi hpip hqqi
    simpa only [hcommon] using ww
  have hDist : Pencil.orbitDistance C1 C0 ≤ (H1 - H0).rank :=
    complement_orbitDistance_contraction E H0 H1 hErank hH0rank hH1rank
      hj0 hj1 hs0 hs1 C0 C1 w0 w1
  have hbound : Pencil.orbitDistance C1 C0 ≤ Fintype.card x := by
    rw [hdiff] at hDist
    exact hDist.trans ((raw_dilation_rank_smul_le (c - d) D).trans hD)
  have hdet : (1 : F) * c - d * 1 ≠ 0 := by simpa using sub_ne_zero.mpr hcd
  have hchange : Pencil.orbitDistance C1 C0 = Pencil.orbitDistance (A0, A1) (B0, B1) := by
    simpa only [C0, C1, Pencil.coefficientChange, one_smul] using
      Pencil.orbitDistance_coefficientChange 1 d 1 c hdet (A0, A1) (B0, B1)
  rw [hchange] at hbound
  exact hbound

end Converse

end MatCP1Converse
