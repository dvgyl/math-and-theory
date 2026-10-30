module

public import MatCP1Converse.ForwardDilationMatrix
public import MatCP1Converse.OrbitDistance
public import MatCP1Converse.StrictCancellation

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Literal left multiplier `diag(P,P,Qi)` on the three-block dilation. -/
def matrixDilationLeft (P : Matrix m m F) (Qi : Matrix n n F) :
    Matrix (m ⊕ (m ⊕ n)) (m ⊕ (m ⊕ n)) F :=
  fromBlocks P 0 0 (fromBlocks P 0 0 Qi)

/-- Literal right multiplier `diag(Q,Q,Pi)` on the three-block dilation. -/
def matrixDilationRight (Q : Matrix n n F) (Pi : Matrix m m F) :
    Matrix (n ⊕ (n ⊕ m)) (n ⊕ (n ⊕ m)) F :=
  fromBlocks Q 0 0 (fromBlocks Q 0 0 Pi)

theorem matrix_dilation_constant_transform
    (B : Matrix m n F) (P Pi : Matrix m m F) (Q Qi : Matrix n n F)
    (hPPi : P * Pi = 1) (hQiQ : Qi * Q = 1) (c d : F) :
    matrixDilationLeft P Qi * matrixDilationConstant B c d * matrixDilationRight Q Pi =
      matrixDilationConstant (P * B * Q) c d := by
  simp [matrixDilationLeft, matrixDilationRight, matrixDilationConstant,
    fromBlocks_multiply, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks,
    fromRows_mul, mul_fromCols, Matrix.mul_smul,
    Matrix.mul_assoc, hPPi, hQiQ]

theorem matrix_dilation_linear_transform
    (B : Matrix m n F) (P Pi : Matrix m m F) (Q Qi : Matrix n n F)
    (hPPi : P * Pi = 1) (hQiQ : Qi * Q = 1) :
    matrixDilationLeft P Qi * matrixDilationLinear B * matrixDilationRight Q Pi =
      matrixDilationLinear (P * B * Q) := by
  simp [matrixDilationLeft, matrixDilationRight, matrixDilationLinear,
    fromBlocks_multiply, Matrix.mul_assoc, hPPi, hQiQ]

namespace Pencil

/-- The native coefficient-pair version of the explicit three-block dilation. -/
def dilate (c d : F) (A : Pencil F m n) :
    Pencil F (m ⊕ (m ⊕ n)) (n ⊕ (n ⊕ m)) :=
  (matrixDilationConstant A.1 c d, matrixDilationLinear A.2)

theorem strictEquivalent_symm {A B : Pencil F m n}
    (h : StrictEquivalent A B) : StrictEquivalent B A := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hAB⟩ := h
  refine ⟨Pi, P, Qi, Q, hPiP, hPPi, hQiQ, hQQi, ?_⟩
  have hrec (M : Matrix m n F) : Pi * (P * M * Q) * Qi = M := by
    simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
  rw [← hAB]
  apply Prod.ext <;> exact hrec _

theorem strictEquivalent_trans {A B C : Pencil F m n}
    (hAB : StrictEquivalent A B) (hBC : StrictEquivalent B C) : StrictEquivalent A C := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, heAB⟩ := hAB
  obtain ⟨U, Ui, V, Vi, hUUi, hUiU, hVVi, hViV, heBC⟩ := hBC
  refine ⟨P * U, Ui * Pi, V * Q, Qi * Vi, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (P * U) * (Ui * Pi) = P * (U * Ui) * Pi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUUi, Matrix.mul_one, hPPi]
  · calc
      (Ui * Pi) * (P * U) = Ui * (Pi * P) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPiP, Matrix.mul_one, hUiU]
  · calc
      (V * Q) * (Qi * Vi) = V * (Q * Qi) * Vi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, Matrix.mul_one, hVVi]
  · calc
      (Qi * Vi) * (V * Q) = Qi * (Vi * V) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hViV, Matrix.mul_one, hQiQ]
  · rw [← heBC] at heAB
    simpa only [transform, Matrix.mul_assoc] using heAB

/-- Constant strict equivalence of the original pencils induces constant
strict equivalence of their dilations. No anchor restriction is needed. -/
theorem strictEquivalent_dilate (c d : F) {A B : Pencil F m n}
    (h : StrictEquivalent A B) : StrictEquivalent (dilate c d A) (dilate c d B) := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hAB⟩ := h
  refine ⟨matrixDilationLeft P Qi, matrixDilationLeft Pi Q,
    matrixDilationRight Q Pi, matrixDilationRight Qi P, ?_, ?_, ?_, ?_, ?_⟩
  · simp [matrixDilationLeft, fromBlocks_multiply, hPPi, hQiQ]
  · simp [matrixDilationLeft, fromBlocks_multiply, hPiP, hQQi]
  · simp [matrixDilationRight, fromBlocks_multiply, hQQi, hPiP]
  · simp [matrixDilationRight, fromBlocks_multiply, hQiQ, hPPi]
  · have h0 : P * B.1 * Q = A.1 := congrArg Prod.fst hAB
    have h1 : P * B.2 * Q = A.2 := congrArg Prod.snd hAB
    apply Prod.ext
    · change matrixDilationLeft P Qi * matrixDilationConstant B.1 c d *
        matrixDilationRight Q Pi = matrixDilationConstant A.1 c d
      rw [matrix_dilation_constant_transform B.1 P Pi Q Qi hPPi hQiQ, h0]
    · change matrixDilationLeft P Qi * matrixDilationLinear B.2 *
        matrixDilationRight Q Pi = matrixDilationLinear A.2
      rw [matrix_dilation_linear_transform B.2 P Pi Q Qi hPPi hQiQ, h1]

/-- The family form of dilation transport supplies the same constant
invertible multipliers for both original coefficient indices. -/
theorem dilate_family_strictEquivalence (c d : F) {A B : Pencil F m n}
    (h : StrictEquivalent A B) :
    FamilyStrictEquivalence (matrixDilationFamily A.1 A.2 c d)
      (matrixDilationFamily B.1 B.2 c d) := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hD⟩ := strictEquivalent_dilate c d h
  refine ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, ?_⟩
  intro j
  cases j
  · exact congrArg Prod.fst hD
  · exact congrArg Prod.snd hD

end Pencil

end MatCP1Converse
