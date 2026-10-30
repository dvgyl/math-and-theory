module

public import MatCP1Converse.OrbitDistance

@[expose] public section

noncomputable section

namespace MatCP1Converse.Pencil

open Matrix

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
theorem generic_transform (P : Matrix m m F) (Q : Matrix n n F)
    (A : Pencil F m n) :
    (transform P Q A).generic = const P * A.generic * const Q := by
  change generic ((P * A.1) * Q, (P * A.2) * Q) = _
  rw [generic_right_mul (P * A.1, P * A.2) Q, generic_left_mul P A]

omit [DecidableEq m] [DecidableEq n] in
theorem normalRank_transform_le (P : Matrix m m F) (Q : Matrix n n F)
    (A : Pencil F m n) :
    (transform P Q A).normalRank ≤ A.normalRank := by
  unfold normalRank
  rw [generic_transform]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The inverse matrices are constant; the normal ranks are the actual ranks
over `F(t)`. The two displayed one-sided inverse identities already suffice. -/
theorem normalRank_transform (P Pi : Matrix m m F) (Q Qi : Matrix n n F)
    (hPiP : Pi * P = 1) (hQQi : Q * Qi = 1) (A : Pencil F m n) :
    (transform P Q A).normalRank = A.normalRank := by
  have hback : transform Pi Qi (transform P Q A) = A := by
    apply Prod.ext <;>
      simp only [transform, Matrix.mul_assoc, ← Matrix.mul_assoc Pi P,
        hPiP, Matrix.one_mul, hQQi, Matrix.mul_one]
  apply le_antisymm (normalRank_transform_le P Q A)
  calc
    A.normalRank = (transform Pi Qi (transform P Q A)).normalRank :=
      congrArg normalRank hback.symm
    _ ≤ (transform P Q A).normalRank := normalRank_transform_le Pi Qi _

theorem normalRank_eq_of_strictEquivalent {A B : Pencil F m n}
    (h : StrictEquivalent A B) : A.normalRank = B.normalRank := by
  obtain ⟨P, Pi, Q, Qi, _, hPiP, hQQi, _, hEq⟩ := h
  rw [← hEq]
  exact normalRank_transform P Pi Q Qi hPiP hQQi B

end MatCP1Converse.Pencil
