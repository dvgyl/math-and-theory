module

public import MatCP1Converse.StaticCompression
public import MatCP1Converse.CoordinateEquivalence

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n m p a b : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p] [Fintype a] [Fintype b]
  [DecidableEq n] [DecidableEq a] [DecidableEq b]

/-- The static-compression theorem for arbitrary prescribed quotient/kernel bases.
Explicit constant invertible left and right matrices align the second pencil so
that its difference from the first has the stated genuine normal-rank bound. -/
theorem static_compression_strict_equivalence_bound
    (A0 A1 : Matrix n n F) (X0 X1 : Matrix n m F) (Y0 Y1 : Matrix p n F)
    (hX0 : Function.Injective X0.mulVec) (hX1 : Function.Injective X1.mulVec)
    (hY0 : Function.Surjective Y0.mulVec) (hY1 : Function.Surjective Y1.mulVec)
    (Q0 Q1 : Matrix a n F) (K0 K1 : Matrix n b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hQ1 : Function.Surjective Q1.mulVec)
    (hK0 : Function.Injective K0.mulVec) (hK1 : Function.Injective K1.mulVec)
    (hker0 : LinearMap.ker Q0.mulVecLin = LinearMap.range X0.mulVecLin)
    (hker1 : LinearMap.ker Q1.mulVecLin = LinearMap.range X1.mulVecLin)
    (hrange0 : LinearMap.range K0.mulVecLin = LinearMap.ker Y0.mulVecLin)
    (hrange1 : LinearMap.range K1.mulVecLin = LinearMap.ker Y1.mulVecLin) :
    ∃ (L Linv : Matrix a a F) (R Rinv : Matrix b b F),
      L * Linv = 1 ∧ Linv * L = 1 ∧ R * Rinv = 1 ∧ Rinv * R = 1 ∧
      Pencil.normalRank
        ((L * Q1 * A1 * K1 * R, L * Q1 * K1 * R) - (Q0 * A0 * K0, Q0 * K0)) ≤
        (fromBlocks (A1 - A0) (X1 - X0) (Y1 - Y0) (0 : Matrix p m F)).rank := by
  obtain ⟨Qt, Kt, hQt, hKt, hkert, hranget, hRank⟩ :=
    exists_valid_static_compression_bound A0 A1 X0 X1 Y0 Y1 hX0 hX1 hY0 hY1 Q0 K0
      hQ0 hK0 hker0 hrange0
  obtain ⟨L, Linv, hLright, hLleft, hL⟩ := exists_quotient_matrix_equivalence
    Q1 Qt hQ1 hQt (hker1.trans hkert.symm)
  obtain ⟨R, Rinv, hRright, hRleft, hR⟩ := exists_kernel_matrix_equivalence
    K1 Kt hK1 hKt (hrange1.trans hranget.symm)
  refine ⟨L, Linv, R, Rinv, hLright, hLleft, hRright, hRleft, ?_⟩
  rw [← hL, ← hR] at hRank
  simpa only [Matrix.mul_assoc] using hRank

end MatCP1Converse
