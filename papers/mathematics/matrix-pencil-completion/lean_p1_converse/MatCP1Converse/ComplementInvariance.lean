module

public import MatCP1Converse.ComplementCoordinates

@[expose] public section

namespace MatCP1Converse

open Matrix

section RankFactorization

variable {F m n r : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

omit [Fintype m] in
/-- Full rank factorizations of the same matrix differ by an actual constant
internal automorphism. Both inverse identities and both factor identities are
proved from the original full-rank and product hypotheses. -/
theorem exists_full_rank_matrix_factorization_equivalence
    (U0 U1 : Matrix m r F) (V0 V1 : Matrix r n F)
    (hU0 : Function.Injective U0.mulVec) (hU1 : Function.Injective U1.mulVec)
    (hV0 : Function.Surjective V0.mulVec) (hV1 : Function.Surjective V1.mulVec)
    (hprod : U0 * V0 = U1 * V1) :
    ∃ D Di : Matrix r r F,
      D * Di = 1 ∧ Di * D = 1 ∧ U0 * D = U1 ∧ Di * V0 = V1 := by
  have heq (v : n → F) : U0 *ᵥ (V0 *ᵥ v) = U1 *ᵥ (V1 *ᵥ v) := by
    simpa only [Matrix.mulVec_mulVec] using congrArg (fun A => A *ᵥ v) hprod
  have hr : LinearMap.range U0.mulVecLin = LinearMap.range U1.mulVecLin := by
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      obtain ⟨z, hz⟩ := hV0 v
      refine ⟨V1 *ᵥ z, ?_⟩
      change U1 *ᵥ (V1 *ᵥ z) = U0 *ᵥ v
      rw [← heq, hz]
    · rintro w ⟨v, rfl⟩
      obtain ⟨z, hz⟩ := hV1 v
      refine ⟨V0 *ᵥ z, ?_⟩
      change U0 *ᵥ (V0 *ᵥ z) = U1 *ᵥ v
      rw [heq, hz]
  obtain ⟨D, Di, hD, hDi, hUD⟩ :=
    exists_kernel_matrix_equivalence U0 U1 hU0 hU1 hr
  have hDV : D * V1 = V0 := by
    apply Matrix.mulVec_injective
    funext v
    apply hU0
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hUD, hprod]
  refine ⟨D, Di, hD, hDi, hUD, ?_⟩
  rw [← hDV, ← Matrix.mul_assoc, hDi, Matrix.one_mul]

end RankFactorization

section Complement

variable {F r s m n a b : Type*} [Field F]
  [Fintype r] [Fintype s] [Fintype m] [Fintype n]
  [Fintype a] [Fintype b]
  [DecidableEq r] [DecidableEq s] [DecidableEq a] [DecidableEq b]

omit [Fintype m] in
/-- Changing only full kernel/quotient coordinates changes both complementary
coefficients by the same constant invertible left and right matrices. -/
theorem complement_coordinate_invariance
    (S : Matrix m (r ⊕ s) F) (T : Matrix (r ⊕ s) n F)
    (Q0 Q1 : Matrix a (r ⊕ s) F) (K0 K1 : Matrix (r ⊕ s) b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hQ1 : Function.Surjective Q1.mulVec)
    (hK0 : Function.Injective K0.mulVec) (hK1 : Function.Injective K1.mulVec)
    (hk0 : LinearMap.ker Q0.mulVecLin = LinearMap.range T.mulVecLin)
    (hk1 : LinearMap.ker Q1.mulVecLin = LinearMap.range T.mulVecLin)
    (hr0 : LinearMap.range K0.mulVecLin = LinearMap.ker S.mulVecLin)
    (hr1 : LinearMap.range K1.mulVecLin = LinearMap.ker S.mulVecLin) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      L * (complementPencil Q1 K1).1 * R = (complementPencil Q0 K0).1 ∧
      L * (complementPencil Q1 K1).2 * R = (complementPencil Q0 K0).2 := by
  obtain ⟨L, Li, hL, hLi, hLQ⟩ := exists_quotient_matrix_equivalence Q1 Q0
    hQ1 hQ0 (hk1.trans hk0.symm)
  obtain ⟨R, Ri, hR, hRi, hKR⟩ := exists_kernel_matrix_equivalence K1 K0
    hK1 hK0 (hr1.trans hr0.symm)
  refine ⟨L, Li, R, Ri, hL, hLi, hR, hRi, ?_, ?_⟩ <;>
    simp only [complementPencil, ← Matrix.mul_assoc, hLQ] <;>
    simp only [Matrix.mul_assoc, hKR]

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
/-- The block-diagonal internal reparametrization commutes with both
coefficient projectors in the actual complementary pencil. -/
theorem complement_internal_transport_coefficients
    (D Di : Matrix r r F) (E Ei : Matrix s s F)
    (hD : D * Di = 1) (hE : E * Ei = 1)
    (Q : Matrix a (r ⊕ s) F) (K : Matrix (r ⊕ s) b F) :
    complementPencil (Q * fromBlocks D 0 0 E) (fromBlocks Di 0 0 Ei * K) =
      complementPencil Q K := by
  have hp0 : fromBlocks D 0 0 E *
      fromBlocks (0 : Matrix r r F) 0 0 (1 : Matrix s s F) *
      fromBlocks Di 0 0 Ei = fromBlocks (0 : Matrix r r F) 0 0 (1 : Matrix s s F) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [hE]
  have hp1 : fromBlocks D 0 0 E *
      fromBlocks (1 : Matrix r r F) 0 0 (0 : Matrix s s F) *
      fromBlocks Di 0 0 Ei = fromBlocks (1 : Matrix r r F) 0 0 (0 : Matrix s s F) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [hD]
  apply Prod.ext
  · change (Q * fromBlocks D 0 0 E) * _ * (fromBlocks Di 0 0 Ei * K) = _
    calc
      _ = Q * (fromBlocks D 0 0 E * fromBlocks 0 0 0 (1 : Matrix s s F) *
          fromBlocks Di 0 0 Ei) * K := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hp0]; rfl
  · change (Q * fromBlocks D 0 0 E) * _ * (fromBlocks Di 0 0 Ei * K) = _
    calc
      _ = Q * (fromBlocks D 0 0 E * fromBlocks (1 : Matrix r r F) 0 0 0 *
          fromBlocks Di 0 0 Ei) * K := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hp1]; rfl

omit [Fintype m] in
/-- Changing both full rank factorizations and both prescribed intrinsic
coordinate maps preserves the constant strict-equivalence class of the actual
complementary pencil. The block-diagonal change is constructed internally. -/
theorem complement_factorization_invariance
    (U0 U1 : Matrix m r F) (V0 V1 : Matrix r n F)
    (X0 X1 : Matrix m s F) (Y0 Y1 : Matrix s n F)
    (hU0 : Function.Injective U0.mulVec) (hU1 : Function.Injective U1.mulVec)
    (hV0 : Function.Surjective V0.mulVec) (hV1 : Function.Surjective V1.mulVec)
    (hX0 : Function.Injective X0.mulVec) (hX1 : Function.Injective X1.mulVec)
    (hY0 : Function.Surjective Y0.mulVec) (hY1 : Function.Surjective Y1.mulVec)
    (hE : U0 * V0 = U1 * V1) (hH : X0 * Y0 = X1 * Y1)
    (Q0 Q1 : Matrix a (r ⊕ s) F) (K0 K1 : Matrix (r ⊕ s) b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hQ1 : Function.Surjective Q1.mulVec)
    (hK0 : Function.Injective K0.mulVec) (hK1 : Function.Injective K1.mulVec)
    (hk0 : LinearMap.ker Q0.mulVecLin = LinearMap.range (fromRows V0 Y0).mulVecLin)
    (hk1 : LinearMap.ker Q1.mulVecLin = LinearMap.range (fromRows V1 Y1).mulVecLin)
    (hr0 : LinearMap.range K0.mulVecLin = LinearMap.ker (fromCols U0 X0).mulVecLin)
    (hr1 : LinearMap.range K1.mulVecLin = LinearMap.ker (fromCols U1 X1).mulVecLin) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      L * (complementPencil Q1 K1).1 * R = (complementPencil Q0 K0).1 ∧
      L * (complementPencil Q1 K1).2 * R = (complementPencil Q0 K0).2 := by
  obtain ⟨D, Di, hD, hDi, hUD, hDiV⟩ :=
    exists_full_rank_matrix_factorization_equivalence U0 U1 V0 V1 hU0 hU1 hV0 hV1 hE
  obtain ⟨J, Ji, hJ, hJi, hXJ, hJiY⟩ :=
    exists_full_rank_matrix_factorization_equivalence X0 X1 Y0 Y1 hX0 hX1 hY0 hY1 hH
  let Z : Matrix (r ⊕ s) (r ⊕ s) F := fromBlocks D 0 0 J
  let Zi : Matrix (r ⊕ s) (r ⊕ s) F := fromBlocks Di 0 0 Ji
  have hZZi : Z * Zi = 1 := by simp [Z, Zi, fromBlocks_multiply, hD, hJ]
  have hZiZ : Zi * Z = 1 := by simp [Z, Zi, fromBlocks_multiply, hDi, hJi]
  have hZT : Zi * fromRows V0 Y0 = fromRows V1 Y1 := by
    simp [Zi, fromBlocks_mul_fromRows, hDiV, hJiY]
  have hSZ : fromCols U1 X1 * Zi = fromCols U0 X0 := by
    simp only [Zi, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add]
    rw [← hUD, ← hXJ]
    simp only [Matrix.mul_assoc, hD, hJ, Matrix.mul_one]
  obtain ⟨hQt, hKt, hkt, hrt⟩ := matrix_transport_quotient_kernel
    (fromRows V0 Y0) (fromRows V1 Y1) (fromCols U0 X0) (fromCols U1 X1)
    Q0 K0 Zi Z Zi Z hZZi hZiZ hZZi hZiZ hZT hSZ hQ0 hK0 hk0 hr0
  obtain ⟨L, Li, R, Ri, hL, hLi, hR, hRi, he0, he1⟩ :=
    complement_coordinate_invariance (fromCols U1 X1) (fromRows V1 Y1)
      (Q0 * Z) Q1 (Zi * K0) K1 hQt hQ1 hKt hK1 hkt hk1 hrt hr1
  have hcoeff : complementPencil (Q0 * Z) (Zi * K0) = complementPencil Q0 K0 :=
    complement_internal_transport_coefficients D Di J Ji hD hJ Q0 K0
  exact ⟨L, Li, R, Ri, hL, hLi, hR, hRi,
    he0.trans (congrArg Prod.fst hcoeff), he1.trans (congrArg Prod.snd hcoeff)⟩

omit [Fintype m] [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- One may prescribe a new pair of full rank factorizations and transport the
intrinsic kernel/quotient coordinates to them while keeping both complementary
coefficient matrices exactly unchanged. -/
theorem complement_transport_factorization
    (U0 U1 : Matrix m r F) (V0 V1 : Matrix r n F)
    (X0 X1 : Matrix m s F) (Y0 Y1 : Matrix s n F)
    (hU0 : Function.Injective U0.mulVec) (hU1 : Function.Injective U1.mulVec)
    (hV0 : Function.Surjective V0.mulVec) (hV1 : Function.Surjective V1.mulVec)
    (hX0 : Function.Injective X0.mulVec) (hX1 : Function.Injective X1.mulVec)
    (hY0 : Function.Surjective Y0.mulVec) (hY1 : Function.Surjective Y1.mulVec)
    (hE : U0 * V0 = U1 * V1) (hH : X0 * Y0 = X1 * Y1)
    (Q0 : Matrix a (r ⊕ s) F) (K0 : Matrix (r ⊕ s) b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hK0 : Function.Injective K0.mulVec)
    (hk0 : LinearMap.ker Q0.mulVecLin = LinearMap.range (fromRows V0 Y0).mulVecLin)
    (hr0 : LinearMap.range K0.mulVecLin = LinearMap.ker (fromCols U0 X0).mulVecLin) :
    ∃ (Q1 : Matrix a (r ⊕ s) F) (K1 : Matrix (r ⊕ s) b F),
      Function.Surjective Q1.mulVec ∧ Function.Injective K1.mulVec ∧
      LinearMap.ker Q1.mulVecLin = LinearMap.range (fromRows V1 Y1).mulVecLin ∧
      LinearMap.range K1.mulVecLin = LinearMap.ker (fromCols U1 X1).mulVecLin ∧
      complementPencil Q1 K1 = complementPencil Q0 K0 := by
  obtain ⟨D, Di, hD, hDi, hUD, hDiV⟩ :=
    exists_full_rank_matrix_factorization_equivalence U0 U1 V0 V1 hU0 hU1 hV0 hV1 hE
  obtain ⟨J, Ji, hJ, hJi, hXJ, hJiY⟩ :=
    exists_full_rank_matrix_factorization_equivalence X0 X1 Y0 Y1 hX0 hX1 hY0 hY1 hH
  let Z : Matrix (r ⊕ s) (r ⊕ s) F := fromBlocks D 0 0 J
  let Zi : Matrix (r ⊕ s) (r ⊕ s) F := fromBlocks Di 0 0 Ji
  have hZZi : Z * Zi = 1 := by simp [Z, Zi, fromBlocks_multiply, hD, hJ]
  have hZiZ : Zi * Z = 1 := by simp [Z, Zi, fromBlocks_multiply, hDi, hJi]
  have hZT : Zi * fromRows V0 Y0 = fromRows V1 Y1 := by
    simp [Zi, fromBlocks_mul_fromRows, hDiV, hJiY]
  have hSZ : fromCols U1 X1 * Zi = fromCols U0 X0 := by
    simp only [Zi, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add]
    rw [← hUD, ← hXJ]
    simp only [Matrix.mul_assoc, hD, hJ, Matrix.mul_one]
  obtain ⟨hQt, hKt, hkt, hrt⟩ := matrix_transport_quotient_kernel
    (fromRows V0 Y0) (fromRows V1 Y1) (fromCols U0 X0) (fromCols U1 X1)
    Q0 K0 Zi Z Zi Z hZZi hZiZ hZZi hZiZ hZT hSZ hQ0 hK0 hk0 hr0
  exact ⟨Q0 * Z, Zi * K0, hQt, hKt, hkt, hrt,
    complement_internal_transport_coefficients D Di J Ji hD hJ Q0 K0⟩

end Complement

end MatCP1Converse
