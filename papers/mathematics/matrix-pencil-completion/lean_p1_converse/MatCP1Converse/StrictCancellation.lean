module

public import MatCP1.MatrixCancellation
public import MatCP1Converse.MatrixExtension

@[expose] public section

namespace MatCP1Converse

variable {F I m n : Type*} [Field F]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A square full-row matrix has an explicit two-sided inverse. -/
theorem square_surjective_inverse (P : Matrix m m F)
    (hP : Function.Surjective P.mulVec) :
    ∃ Pi : Matrix m m F, P * Pi = 1 ∧ Pi * P = 1 := by
  classical
  have hi : Function.Injective P.mulVecLin := LinearMap.injective_iff_surjective.mpr hP
  let e : (m → F) ≃ₗ[F] (m → F) := LinearEquiv.ofBijective P.mulVecLin ⟨hi, hP⟩
  have he : LinearMap.toMatrix' e.toLinearMap = P := by
    change LinearMap.toMatrix' P.mulVecLin = P
    simpa only [Matrix.toLin'_apply'] using LinearMap.toMatrix'_toLin' P
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · simpa only [he] using toMatrix_equiv_mul_symm e
  · simpa only [LinearEquiv.symm_symm, he] using toMatrix_equiv_mul_symm e.symm

/-- A square full-column matrix has an explicit two-sided inverse. -/
theorem square_injective_inverse (Q : Matrix n n F)
    (hQ : Function.Injective Q.mulVec) :
    ∃ Qi : Matrix n n F, Q * Qi = 1 ∧ Qi * Q = 1 := by
  have hs : Function.Surjective Q.mulVecLin := LinearMap.injective_iff_surjective.mp hQ
  exact square_surjective_inverse Q hs

/-- Constant strict equivalence of arbitrary rectangular matrix families, with both
inverse matrices supplied as witnesses. -/
def FamilyStrictEquivalence (A B : I → Matrix m n F) : Prop :=
  ∃ (P Pi : Matrix m m F) (Q Qi : Matrix n n F),
    P * Pi = 1 ∧ Pi * P = 1 ∧ Q * Qi = 1 ∧ Qi * Q = 1 ∧
      ∀ i, P * B i * Q = A i

/-- For equal-sized families, full-row/full-column compression is exactly strict
equivalence, including every zero-dimensional case. -/
theorem familyStrictEquivalence_iff_matrixCompression (A B : I → Matrix m n F) :
    FamilyStrictEquivalence A B ↔ MatCP1.MatrixJointCompression A B := by
  constructor
  · rintro ⟨P, Pi, Q, Qi, hPPi, _, _, hQiQ, hAB⟩
    have hp : P.mulVecLin.comp Pi.mulVecLin = LinearMap.id := by
      simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hPPi
    have hq : Qi.mulVecLin.comp Q.mulVecLin = LinearMap.id := by
      simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hQiQ
    have hPs : Function.Surjective P.mulVecLin := by
      intro v
      exact ⟨Pi.mulVecLin v, LinearMap.congr_fun hp v⟩
    have hQi : Function.LeftInverse Qi.mulVecLin Q.mulVecLin :=
      fun v => LinearMap.congr_fun hq v
    exact ⟨P, Q, hPs, hQi.injective, hAB⟩
  · rintro ⟨P, Q, hP, hQ, hAB⟩
    obtain ⟨Pi, hPPi, hPiP⟩ := square_surjective_inverse P hP
    obtain ⟨Qi, hQQi, hQiQ⟩ := square_injective_inverse Q hQ
    exact ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hAB⟩

variable {u v : Type*} [Fintype u] [Fintype v] [DecidableEq u] [DecidableEq v]

/-- Common-summand cancellation for strict equivalence follows from the proved
compression cancellation and does not invoke Kronecker canonical form or uniqueness. -/
theorem familyStrictEquivalence_common_summand_iff [Infinite F]
    (A B : I → Matrix m n F) (S : I → Matrix u v F) :
    FamilyStrictEquivalence (fun i => Matrix.fromBlocks (A i) 0 0 (S i))
      (fun i => Matrix.fromBlocks (B i) 0 0 (S i)) ↔ FamilyStrictEquivalence A B := by
  rw [familyStrictEquivalence_iff_matrixCompression,
    familyStrictEquivalence_iff_matrixCompression]
  exact MatCP1.matrixJointCompression_common_summand_iff A B S

/-- Fully exposed strict-equivalence cancellation: every inverse and every family
coefficient equation is an explicit hypothesis or conclusion. -/
theorem strict_common_summand_cancellation [Infinite F]
    (A B : I → Matrix m n F) (S : I → Matrix u v F)
    (P Pi : Matrix (m ⊕ u) (m ⊕ u) F) (Q Qi : Matrix (n ⊕ v) (n ⊕ v) F)
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    (hQQi : Q * Qi = 1) (hQiQ : Qi * Q = 1)
    (hAB : ∀ i, P * Matrix.fromBlocks (B i) 0 0 (S i) * Q =
      Matrix.fromBlocks (A i) 0 0 (S i)) :
    ∃ (P' Pi' : Matrix m m F) (Q' Qi' : Matrix n n F),
      P' * Pi' = 1 ∧ Pi' * P' = 1 ∧ Q' * Qi' = 1 ∧ Qi' * Q' = 1 ∧
        ∀ i, P' * B i * Q' = A i :=
  (familyStrictEquivalence_common_summand_iff A B S).mp
    ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hAB⟩

end MatCP1Converse
