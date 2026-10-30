module

public import MatCP1Converse.ParameterChange

@[expose] public section

noncomputable section

namespace MatCP1Converse.Pencil

open Matrix

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- A simultaneous constant change of the two coefficient matrices. -/
def transform (P : Matrix m m F) (Q : Matrix n n F) (A : Pencil F m n) : Pencil F m n :=
  (P * A.1 * Q, P * A.2 * Q)

/-- Strict equivalence with actual constant matrices and two-sided inverses. -/
def StrictEquivalent (A B : Pencil F m n) : Prop :=
  ∃ (P Pi : Matrix m m F) (Q Qi : Matrix n n F),
    P * Pi = 1 ∧ Pi * P = 1 ∧ Q * Qi = 1 ∧ Qi * Q = 1 ∧ transform P Q B = A

theorem strictEquivalent_refl (A : Pencil F m n) : StrictEquivalent A A := by
  exact ⟨1, 1, 1, 1, by simp, by simp, by simp, by simp, by simp [transform]⟩

omit [DecidableEq m] [DecidableEq n] in
theorem coefficientChange_transform (a b c d : F)
    (P : Matrix m m F) (Q : Matrix n n F) (A : Pencil F m n) :
    coefficientChange a b c d (transform P Q A) =
      transform P Q (coefficientChange a b c d A) := by
  apply Prod.ext <;>
    simp [coefficientChange, transform, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]

/-- A homogeneous parameter change preserves and reflects strict equivalence;
the witnessing matrices remain constant. -/
theorem strictEquivalent_coefficientChange_iff (a b c d : F)
    (hdet : a * d - b * c ≠ 0) (A B : Pencil F m n) :
    StrictEquivalent (coefficientChange a b c d A) (coefficientChange a b c d B) ↔
      StrictEquivalent A B := by
  constructor
  · rintro ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, heq⟩
    refine ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, ?_⟩
    apply coefficientChange_injective a b c d hdet
    rw [coefficientChange_transform]
    exact heq
  · rintro ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, heq⟩
    refine ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, ?_⟩
    rw [← coefficientChange_transform, heq]

/-- A bound on the minimum normal-rank difference between the two complete
constant strict-equivalence classes. Both representatives are quantified. -/
def BoundedDistance (A B : Pencil F m n) (x : ℕ) : Prop :=
  ∃ A' B' : Pencil F m n,
    StrictEquivalent A' A ∧ StrictEquivalent B' B ∧ normalRank (A' - B') ≤ x

theorem boundedDistance_mono (A B : Pencil F m n) {x y : ℕ}
    (h : BoundedDistance A B x) (hxy : x ≤ y) : BoundedDistance A B y := by
  obtain ⟨A', B', hA, hB, hR⟩ := h
  exact ⟨A', B', hA, hB, hR.trans hxy⟩

/-- The actual orbit rank-distance bound is invariant under every invertible
homogeneous coefficient transformation. -/
theorem boundedDistance_coefficientChange_iff (a b c d : F)
    (hdet : a * d - b * c ≠ 0) (A B : Pencil F m n) (x : ℕ) :
    BoundedDistance (coefficientChange a b c d A) (coefficientChange a b c d B) x ↔
      BoundedDistance A B x := by
  constructor
  · rintro ⟨A', B', hA, hB, hR⟩
    obtain ⟨A0, rfl⟩ := coefficientChange_surjective a b c d hdet A'
    obtain ⟨B0, rfl⟩ := coefficientChange_surjective a b c d hdet B'
    refine ⟨A0, B0,
      (strictEquivalent_coefficientChange_iff a b c d hdet A0 A).mp hA,
      (strictEquivalent_coefficientChange_iff a b c d hdet B0 B).mp hB, ?_⟩
    rw [← coefficientChange_sub, normalRank_coefficientChange a b c d hdet] at hR
    exact hR
  · rintro ⟨A', B', hA, hB, hR⟩
    refine ⟨coefficientChange a b c d A', coefficientChange a b c d B',
      (strictEquivalent_coefficientChange_iff a b c d hdet A' A).mpr hA,
      (strictEquivalent_coefficientChange_iff a b c d hdet B' B).mpr hB, ?_⟩
    rw [← coefficientChange_sub, normalRank_coefficientChange a b c d hdet]
    exact hR

theorem exists_boundedDistance (A B : Pencil F m n) : ∃ x, BoundedDistance A B x :=
  ⟨normalRank (A - B), A, B, strictEquivalent_refl A, strictEquivalent_refl B, le_rfl⟩

/-- The actual minimum, taken over every pair of constant-equivalent
representatives. It is not a sampled or chosen-representative distance. -/
def orbitDistance (A B : Pencil F m n) : ℕ := by
  classical
  exact Nat.find (exists_boundedDistance A B)

theorem orbitDistance_le_iff (A B : Pencil F m n) (x : ℕ) :
    orbitDistance A B ≤ x ↔ BoundedDistance A B x := by
  classical
  constructor
  · intro h
    exact boundedDistance_mono A B (Nat.find_spec (exists_boundedDistance A B)) h
  · intro h
    exact Nat.find_min' (exists_boundedDistance A B) h

/-- The minimum itself is preserved, with all strict-equivalence witnesses
and normal ranks interpreted literally. -/
theorem orbitDistance_coefficientChange (a b c d : F)
    (hdet : a * d - b * c ≠ 0) (A B : Pencil F m n) :
    orbitDistance (coefficientChange a b c d A) (coefficientChange a b c d B) =
      orbitDistance A B := by
  apply le_antisymm
  · apply (orbitDistance_le_iff _ _ _).mpr
    apply (boundedDistance_coefficientChange_iff a b c d hdet A B _).mpr
    exact (orbitDistance_le_iff A B _).mp le_rfl
  · apply (orbitDistance_le_iff A B _).mpr
    apply (boundedDistance_coefficientChange_iff a b c d hdet A B _).mp
    exact (orbitDistance_le_iff _ _ _).mp le_rfl

end MatCP1Converse.Pencil
