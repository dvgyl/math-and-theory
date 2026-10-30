module

public import MatCP1Converse.ComplementNormalization

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

/-- Literal sum-indexed matrices in product coordinates. -/
def complementBlockMap (H : Matrix (n ⊕ p) (n ⊕ m) F) :
    ((n → F) × (m → F)) →ₗ[F] ((n → F) × (p → F)) :=
  (LinearEquiv.sumArrowLequivProdArrow n p F F).toLinearMap.comp
    (H.mulVecLin.comp (LinearEquiv.sumArrowLequivProdArrow n m F F).symm.toLinearMap)

theorem complementBlockMap_apply
    (H : Matrix (n ⊕ p) (n ⊕ m) F) (v : n → F) (w : m → F) :
    complementBlockMap H (v, w) =
      ((H *ᵥ Sum.elim v w) ∘ Sum.inl, (H *ᵥ Sum.elim v w) ∘ Sum.inr) := rfl

/-- The actual matrix-rank hypothesis gives the common graph chart; the
graph choices are constructed by the already proved infinite-field argument. -/
theorem exists_common_complement_graph [Infinite F]
    (H0 H1 : Matrix (n ⊕ p) (n ⊕ m) F)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n) :
    ∃ (U : Matrix n p F) (V : Matrix m n F),
      Function.Bijective
        (fromCols (1 : Matrix n n F) U * H0 * fromRows (1 : Matrix n n F) V).mulVec ∧
      Function.Bijective
        (fromCols (1 : Matrix n n F) U * H1 * fromRows (1 : Matrix n n F) V).mulVec := by
  have hrank (H : Matrix (n ⊕ p) (n ⊕ m) F) (hH : H.rank = Fintype.card n) :
      Module.finrank F (LinearMap.range (complementBlockMap H)) =
        Module.finrank F (n → F) := by
    unfold complementBlockMap
    rw [LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top H.mulVecLin
        (LinearEquiv.sumArrowLequivProdArrow n m F F).symm.range]
    exact ((LinearEquiv.sumArrowLequivProdArrow n p F F).finrank_map_eq _).trans
      (hH.trans (Module.finrank_fintype_fun_eq_card (R := F)).symm)
  obtain ⟨u, v, hbij0, hbij1⟩ := exists_common_rank_chart
    (complementBlockMap H0) (complementBlockMap H1) (hrank H0 h0) (hrank H1 h1)
  let U := LinearMap.toMatrix' u
  let V := LinearMap.toMatrix' v
  have hu (x : p → F) : U *ᵥ x = u x := by
    change Matrix.toLin' (LinearMap.toMatrix' u) x = u x
    rw [Matrix.toLin'_toMatrix']
  have hv (x : n → F) : V *ᵥ x = v x := by
    change Matrix.toLin' (LinearMap.toMatrix' v) x = v x
    rw [Matrix.toLin'_toMatrix']
  have hgraph (H : Matrix (n ⊕ p) (n ⊕ m) F) :
      (fromCols (1 : Matrix n n F) U * H * fromRows (1 : Matrix n n F) V).mulVecLin =
        (LinearMap.id.coprod u).comp ((complementBlockMap H).comp (LinearMap.id.prod v)) := by
    apply LinearMap.ext
    intro x
    change (fromCols (1 : Matrix n n F) U * H * fromRows (1 : Matrix n n F) V) *ᵥ x = _
    simp only [← Matrix.mulVec_mulVec, fromCols_mulVec, fromRows_mulVec,
      Matrix.one_mulVec, hu, hv, LinearMap.comp_apply, LinearMap.prod_apply,
      LinearMap.id_apply, complementBlockMap_apply, LinearMap.coprod_apply]
    rfl
  refine ⟨U, V, ?_, ?_⟩
  · change Function.Bijective
      (fromCols (1 : Matrix n n F) U * H0 * fromRows (1 : Matrix n n F) V).mulVecLin
    rw [hgraph]
    exact hbij0
  · change Function.Bijective
      (fromCols (1 : Matrix n n F) U * H1 * fromRows (1 : Matrix n n F) V).mulVecLin
    rw [hgraph]
    exact hbij1

/-- Turning a proved bijective square matrix into a literal two-sided inverse. -/
theorem complement_matrix_inverse_of_bijective
    (G : Matrix n n F) (hG : Function.Bijective G.mulVec) :
    ∃ Gi : Matrix n n F, Gi * G = 1 ∧ G * Gi = 1 := by
  let e := LinearEquiv.ofBijective G.mulVecLin hG
  have he : LinearMap.toMatrix' e.toLinearMap = G := by
    change LinearMap.toMatrix' G.mulVecLin = G
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · rw [← he]
    exact toMatrix_equiv_mul_symm e.symm
  · rw [← he]
    exact toMatrix_equiv_mul_symm e

/-- Actual rank is preserved by the displayed constant invertible multipliers. -/
theorem complement_rank_constant_equivalence
    (H : Matrix (n ⊕ p) (n ⊕ m) F)
    (P Pi : Matrix (n ⊕ p) (n ⊕ p) F)
    (Q Qi : Matrix (n ⊕ m) (n ⊕ m) F)
    (hPiP : Pi * P = 1) (hQQi : Q * Qi = 1) :
    (P * H * Q).rank = H.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have heq : Pi * (P * H * Q) * Qi = H := by
      simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    calc
      H.rank = (Pi * (P * H * Q) * Qi).rank := congrArg Matrix.rank heq.symm
      _ ≤ (P * H * Q).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Two arbitrary matrices of actual rank `card n` have one common pair of
constant shears preserving `diag(I,0)` and putting both into completed pivot
charts. The inverses and Schur-completed blocks are all constructed here. -/
theorem exists_common_complement_completed_chart [Infinite F]
    (H0 H1 : Matrix (n ⊕ p) (n ⊕ m) F)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n) :
    ∃ (P Pi : Matrix (n ⊕ p) (n ⊕ p) F)
      (Q Qi : Matrix (n ⊕ m) (n ⊕ m) F)
      (G0 Gi0 G1 Gi1 : Matrix n n F) (B0 B1 : Matrix n m F) (C0 C1 : Matrix p n F),
      P * Pi = 1 ∧ Pi * P = 1 ∧ Q * Qi = 1 ∧ Qi * Q = 1 ∧
      P * fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) * Q =
        fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) ∧
      Gi0 * G0 = 1 ∧ G0 * Gi0 = 1 ∧ Gi1 * G1 = 1 ∧ G1 * Gi1 = 1 ∧
      P * H0 * Q = completedBlock G0 Gi0 B0 C0 ∧
      P * H1 * Q = completedBlock G1 Gi1 B1 C1 := by
  obtain ⟨U, V, hG0, hG1⟩ := exists_common_complement_graph H0 H1 h0 h1
  let P : Matrix (n ⊕ p) (n ⊕ p) F := fromBlocks 1 U 0 1
  let Pi : Matrix (n ⊕ p) (n ⊕ p) F := fromBlocks 1 (-U) 0 1
  let Q : Matrix (n ⊕ m) (n ⊕ m) F := fromBlocks 1 0 V 1
  let Qi : Matrix (n ⊕ m) (n ⊕ m) F := fromBlocks 1 0 (-V) 1
  have hPPi : P * Pi = 1 := by simp [P, Pi, fromBlocks_multiply]
  have hPiP : Pi * P = 1 := by simp [P, Pi, fromBlocks_multiply]
  have hQQi : Q * Qi = 1 := by simp [Q, Qi, fromBlocks_multiply]
  have hQiQ : Qi * Q = 1 := by simp [Q, Qi, fromBlocks_multiply]
  have hE : P * fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) * Q =
      fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) := by
    simp [P, Q, fromBlocks_multiply]
  have htop (H : Matrix (n ⊕ p) (n ⊕ m) F) :
      (P * H * Q).toBlocks₁₁ =
        fromCols (1 : Matrix n n F) U * H * fromRows (1 : Matrix n n F) V := by
    rw [← fromBlocks_toBlocks H]
    simp [P, Q, fromBlocks_multiply, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  let M0 := P * H0 * Q
  let M1 := P * H1 * Q
  have hb0 : Function.Bijective M0.toBlocks₁₁.mulVec := by
    dsimp [M0]
    rw [htop]
    exact hG0
  have hb1 : Function.Bijective M1.toBlocks₁₁.mulVec := by
    dsimp [M1]
    rw [htop]
    exact hG1
  obtain ⟨Gi0, hGi0, hG0i⟩ := complement_matrix_inverse_of_bijective M0.toBlocks₁₁ hb0
  obtain ⟨Gi1, hGi1, hG1i⟩ := complement_matrix_inverse_of_bijective M1.toBlocks₁₁ hb1
  have hcomplete (H : Matrix (n ⊕ p) (n ⊕ m) F)
      (Gi : Matrix n n F) (hGi : Gi * (P * H * Q).toBlocks₁₁ = 1)
      (hH : H.rank = Fintype.card n) :
      P * H * Q = completedBlock (P * H * Q).toBlocks₁₁ Gi
        (P * H * Q).toBlocks₁₂ (P * H * Q).toBlocks₂₁ := by
    let M := P * H * Q
    have hM : M.rank = Fintype.card n :=
      (complement_rank_constant_equivalence H P Pi Q Qi hPiP hQQi).trans hH
    have hD : M.toBlocks₂₂ = M.toBlocks₂₁ * Gi * M.toBlocks₁₂ :=
      matrix_block_completed_of_rank M.toBlocks₁₁ Gi M.toBlocks₁₂ M.toBlocks₂₁
        M.toBlocks₂₂ hGi (by rw [fromBlocks_toBlocks]; exact hM)
    change M = completedBlock M.toBlocks₁₁ Gi M.toBlocks₁₂ M.toBlocks₂₁
    calc
      M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
        (fromBlocks_toBlocks M).symm
      _ = _ := by rw [hD]; rfl
  exact ⟨P, Pi, Q, Qi, M0.toBlocks₁₁, Gi0, M1.toBlocks₁₁, Gi1,
    M0.toBlocks₁₂, M1.toBlocks₁₂, M0.toBlocks₂₁, M1.toBlocks₂₁,
    hPPi, hPiP, hQQi, hQiQ, hE, hGi0, hG0i, hGi1, hG1i,
    hcomplete H0 Gi0 hGi0 h0, hcomplete H1 Gi1 hGi1 h1⟩

end MatCP1Converse
