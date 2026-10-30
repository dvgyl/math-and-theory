module

public import MatCP1Converse.StaticEquivalence
public import MatCP1Converse.PrincipalPivot

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m a b : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m] [Fintype a] [Fintype b]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]
  [DecidableEq a] [DecidableEq b]

/-- Combining the exact principal-pivot rank identity with the full static
compression theorem gives the actual contraction in an invertible common chart.
The outer left and right changes of the compressed pencil are constant. -/
theorem pivot_compression_strict_equivalence_bound
    (G0 G0inv G1 G1inv : Matrix n n F)
    (B0 B1 : Matrix n m F) (C0 C1 : Matrix p n F)
    (h0left : G0inv * G0 = 1) (h0right : G0 * G0inv = 1)
    (h1left : G1inv * G1 = 1) (h1right : G1 * G1inv = 1)
    (hB0 : Function.Injective B0.mulVec) (hB1 : Function.Injective B1.mulVec)
    (hC0 : Function.Surjective C0.mulVec) (hC1 : Function.Surjective C1.mulVec)
    (Q0 Q1 : Matrix a n F) (K0 K1 : Matrix n b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hQ1 : Function.Surjective Q1.mulVec)
    (hK0 : Function.Injective K0.mulVec) (hK1 : Function.Injective K1.mulVec)
    (hker0 : LinearMap.ker Q0.mulVecLin = LinearMap.range (G0inv * B0).mulVecLin)
    (hker1 : LinearMap.ker Q1.mulVecLin = LinearMap.range (G1inv * B1).mulVecLin)
    (hrange0 : LinearMap.range K0.mulVecLin = LinearMap.ker (C0 * G0inv).mulVecLin)
    (hrange1 : LinearMap.range K1.mulVecLin = LinearMap.ker (C1 * G1inv).mulVecLin) :
    ∃ (L Linv : Matrix a a F) (R Rinv : Matrix b b F),
      L * Linv = 1 ∧ Linv * L = 1 ∧ R * Rinv = 1 ∧ Rinv * R = 1 ∧
      Pencil.normalRank
        ((L * Q1 * G1inv * K1 * R, L * Q1 * K1 * R) -
          (Q0 * G0inv * K0, Q0 * K0)) ≤
        (completedBlock G1 G1inv B1 C1 - completedBlock G0 G0inv B0 C0).rank := by
  have hX (G Gi : Matrix n n F) (B : Matrix n m F)
      (hG : G * Gi = 1) (hB : Function.Injective B.mulVec) :
      Function.Injective (-(Gi * B)).mulVec := by
    intro x y hxy
    apply hB
    have hh := congrArg (fun v : n → F => G *ᵥ v) (neg_injective
      (by simpa only [Matrix.neg_mulVec] using hxy))
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hG, Matrix.one_mul] using hh
  have hY (G Gi : Matrix n n F) (C : Matrix p n F)
      (hG : Gi * G = 1) (hC : Function.Surjective C.mulVec) :
      Function.Surjective (C * Gi).mulVec := by
    intro y
    obtain ⟨v, hv⟩ := hC y
    refine ⟨G *ᵥ v, ?_⟩
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hG, Matrix.mul_one] using hv
  have hRangeNeg (B : Matrix n m F) :
      LinearMap.range (-B).mulVecLin = LinearMap.range B.mulVecLin := by
    have heq : (-B).mulVecLin = -B.mulVecLin := by
      apply LinearMap.ext
      intro x
      exact Matrix.neg_mulVec x B
    rw [heq, LinearMap.range_neg]
  obtain ⟨L, Linv, R, Rinv, hLl, hLr, hRl, hRr, hRank⟩ :=
    static_compression_strict_equivalence_bound G0inv G1inv
      (-(G0inv * B0)) (-(G1inv * B1)) (C0 * G0inv) (C1 * G1inv)
      (hX G0 G0inv B0 h0right hB0) (hX G1 G1inv B1 h1right hB1)
      (hY G0 G0inv C0 h0left hC0) (hY G1 G1inv C1 h1left hC1)
      Q0 Q1 K0 K1 hQ0 hQ1 hK0 hK1
      (hker0.trans (hRangeNeg _).symm) (hker1.trans (hRangeNeg _).symm)
      hrange0 hrange1
  refine ⟨L, Linv, R, Rinv, hLl, hLr, hRl, hRr, ?_⟩
  have hblock : fromBlocks (G1inv - G0inv)
      (-(G1inv * B1) - -(G0inv * B0)) (C1 * G1inv - C0 * G0inv)
      (0 : Matrix p m F) = principalPivot G1inv B1 C1 - principalPivot G0inv B0 C0 := by
    ext i j
    cases i <;> cases j <;> simp [principalPivot, fromBlocks]
  rw [hblock, principalPivot_sub_rank G0 G0inv G1 G1inv B0 B1 C0 C1
    h0left h0right h1left h1right] at hRank
  exact hRank

end MatCP1Converse
