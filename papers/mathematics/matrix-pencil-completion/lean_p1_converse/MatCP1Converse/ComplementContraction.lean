module

public import MatCP1Converse.ComplementCommonChart
public import MatCP1Converse.ComplementPresentation
public import MatCP1Converse.RankNormalization

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m a b : Type*} [Field F] [Infinite F]
  [Fintype n] [Fintype p] [Fintype m] [Fintype a] [Fintype b]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]
  [DecidableEq a] [DecidableEq b]

/-- Full intrinsic contraction with only the common coefficient already in
rank normal form. The common pivot chart, completed lower blocks, all full
border ranks and the intrinsic/static correspondence are proved internally. -/
theorem complement_normalized_coefficient_contraction
    (H0 H1 : Matrix (n ⊕ p) (n ⊕ m) F)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n)
    (hj0 : Function.Injective (fromRows
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H0).mulVec)
    (hj1 : Function.Injective (fromRows
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H1).mulVec)
    (hs0 : Function.Surjective (fromCols
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H0).mulVec)
    (hs1 : Function.Surjective (fromCols
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H1).mulVec)
    (A0 A1 : Pencil F a b)
    (w0 : ComplementPresentation n n
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H0 A0)
    (w1 : ComplementPresentation n n
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F)) H1 A1) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      Pencil.normalRank ((L * A1.1 * R, L * A1.2 * R) - A0) ≤ (H1 - H0).rank := by
  obtain ⟨P, Pi, Q, Qi, G0, Gi0, G1, Gi1, B0, B1, C0, C1,
    hPPi, hPiP, hQQi, hQiQ, hE, hGi0, hG0i, hGi1, hG1i, hM0, hM1⟩ :=
    exists_common_complement_completed_chart H0 H1 h0 h1
  let E : Matrix (n ⊕ p) (n ⊕ m) F := fromBlocks 1 0 0 0
  have hinj0 : Function.Injective (fromRows E (completedBlock G0 Gi0 B0 C0)).mulVec := by
    simpa only [E, hE, hM0] using
      complement_joint_injective_transport E H0 P Pi Q Qi hPiP hQiQ hj0
  have hinj1 : Function.Injective (fromRows E (completedBlock G1 Gi1 B1 C1)).mulVec := by
    simpa only [E, hE, hM1] using
      complement_joint_injective_transport E H1 P Pi Q Qi hPiP hQiQ hj1
  have hsurj0 : Function.Surjective (fromCols E (completedBlock G0 Gi0 B0 C0)).mulVec := by
    simpa only [E, hE, hM0] using
      complement_joint_surjective_transport E H0 P Pi Q Qi hPPi hQQi hs0
  have hsurj1 : Function.Surjective (fromCols E (completedBlock G1 Gi1 B1 C1)).mulVec := by
    simpa only [E, hE, hM1] using
      complement_joint_surjective_transport E H1 P Pi Q Qi hPPi hQQi hs1
  have hB0 := complement_chartB_injective_of_joint G0 Gi0 B0 C0 hinj0
  have hB1 := complement_chartB_injective_of_joint G1 Gi1 B1 C1 hinj1
  have hC0 := complement_chartC_surjective_of_joint G0 Gi0 B0 C0 hsurj0
  have hC1 := complement_chartC_surjective_of_joint G1 Gi1 B1 C1 hsurj1
  have wt0 : ComplementPresentation n n E (completedBlock G0 Gi0 B0 C0) A0 := by
    simpa only [hE, hM0] using w0.ambient P Pi Q Qi hPiP hQQi
  have wt1 : ComplementPresentation n n E (completedBlock G1 Gi1 B1 C1) A1 := by
    simpa only [hE, hM1] using w1.ambient P Pi Q Qi hPiP hQQi
  obtain ⟨Q0, K0, hQ0, hK0, hk0, hr0, hc0⟩ :=
    complement_presentation_chart_coordinates G0 Gi0 B0 C0 hGi0 hG0i A0 wt0
  obtain ⟨Q1, K1, hQ1, hK1, hk1, hr1, hc1⟩ :=
    complement_presentation_chart_coordinates G1 Gi1 B1 C1 hGi1 hG1i A1 wt1
  obtain ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, hRank⟩ :=
    complement_chart_contraction G0 Gi0 G1 Gi1 B0 B1 C0 C1 hGi0 hG0i hGi1 hG1i
      hB0 hB1 hC0 hC1 Q0 Q1 K0 K1 hQ0 hQ1 hK0 hK1 hk0 hk1 hr0 hr1
  refine ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, ?_⟩
  rw [hc0, hc1, ← hM0, ← hM1, ← Matrix.sub_mul, ← Matrix.mul_sub,
    complement_rank_constant_equivalence (H1 - H0) P Pi Q Qi hPiP hQQi] at hRank
  exact hRank

/-- Intrinsic common-coefficient rank contraction for arbitrary rectangular
matrices at their actual coefficient ranks. There are no assumed common
charts, pivot blocks, Schur completions, derivative conditions, or construction
correspondences. The full quotient/kernel data are exactly a presentation of
the complementary pencil, and may be prescribed arbitrarily.

Joint injectivity states the absence of a common constant right kernel; joint
surjectivity states that the two coefficient ranges span the target. Both
conditions are imposed on the original matrices, before any normalization. -/
theorem complement_common_coefficient_contraction
    (E H0 H1 : Matrix (n ⊕ p) (n ⊕ m) F)
    (hE : E.rank = Fintype.card n)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n)
    (hj0 : Function.Injective (fromRows E H0).mulVec)
    (hj1 : Function.Injective (fromRows E H1).mulVec)
    (hs0 : Function.Surjective (fromCols E H0).mulVec)
    (hs1 : Function.Surjective (fromCols E H1).mulVec)
    (A0 A1 : Pencil F a b)
    (w0 : ComplementPresentation n n E H0 A0)
    (w1 : ComplementPresentation n n E H1 A1) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      Pencil.normalRank ((L * A1.1 * R, L * A1.2 * R) - A0) ≤ (H1 - H0).rank := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hnorm⟩ :=
    exists_rectangular_rank_normalization E hE
  have hR0 : (P * H0 * Q).rank = Fintype.card n :=
    (complement_rank_constant_equivalence H0 P Pi Q Qi hPiP hQQi).trans h0
  have hR1 : (P * H1 * Q).rank = Fintype.card n :=
    (complement_rank_constant_equivalence H1 P Pi Q Qi hPiP hQQi).trans h1
  have htj0 := complement_joint_injective_transport E H0 P Pi Q Qi hPiP hQiQ hj0
  have htj1 := complement_joint_injective_transport E H1 P Pi Q Qi hPiP hQiQ hj1
  have hts0 := complement_joint_surjective_transport E H0 P Pi Q Qi hPPi hQQi hs0
  have hts1 := complement_joint_surjective_transport E H1 P Pi Q Qi hPPi hQQi hs1
  rw [hnorm] at htj0 htj1 hts0 hts1
  have wt0 := w0.ambient P Pi Q Qi hPiP hQQi
  have wt1 := w1.ambient P Pi Q Qi hPiP hQQi
  rw [hnorm] at wt0 wt1
  obtain ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, hRank⟩ :=
    complement_normalized_coefficient_contraction (P * H0 * Q) (P * H1 * Q)
      hR0 hR1 htj0 htj1 hts0 hts1 A0 A1 wt0 wt1
  refine ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, ?_⟩
  rw [← Matrix.sub_mul, ← Matrix.mul_sub,
    complement_rank_constant_equivalence (H1 - H0) P Pi Q Qi hPiP hQQi] at hRank
  exact hRank

end MatCP1Converse
