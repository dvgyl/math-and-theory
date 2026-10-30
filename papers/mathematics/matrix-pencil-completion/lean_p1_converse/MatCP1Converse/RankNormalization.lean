module

public import MatCP1Converse.RankChart
public import MatCP1Converse.MatrixExtension
public import MatCP1Converse.Pencil
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

noncomputable section

namespace MatCP1Converse

open Matrix

section General

variable {F r s k : Type*} [Field F]
  [Fintype r] [Fintype s] [Fintype k]
  [DecidableEq r] [DecidableEq s] [DecidableEq k]

/-- Full matrix rank factorizations through a prescribed finite index type of
the actual rank, with injection and surjection included in the conclusion. -/
theorem exists_matrix_full_rank_factorization (E : Matrix r s F)
    (hRank : E.rank = Fintype.card k) :
    ∃ (U : Matrix r k F) (V : Matrix k s F),
      Function.Injective U.mulVec ∧ Function.Surjective V.mulVec ∧ U * V = E := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_full_rank_factorization (V := k → F)
    E.mulVecLin (by simpa only [Matrix.rank, Module.finrank_pi] using hRank)
  refine ⟨LinearMap.toMatrix' u, LinearMap.toMatrix' v, ?_, ?_, ?_⟩
  · intro x y h
    apply hu
    simpa only [LinearMap.toMatrix'_mulVec] using h
  · intro y
    obtain ⟨x, hx⟩ := hv y
    exact ⟨x, by simpa only [LinearMap.toMatrix'_mulVec] using hx⟩
  · have hh := congrArg LinearMap.toMatrix' huv
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] using hh

/-- Every actual-rank factorization can be normalized to any prescribed full
embedding and full quotient of the same rank. All changes are constant and
explicit two-sided inverses are returned. -/
theorem matrix_rank_factor_normalize (E : Matrix r s F)
    (U0 : Matrix r k F) (V0 : Matrix k s F)
    (hRank : E.rank = Fintype.card k)
    (hU0 : Function.Injective U0.mulVec) (hV0 : Function.Surjective V0.mulVec) :
    ∃ (P Pi : Matrix r r F) (Q Qi : Matrix s s F),
      P * Pi = 1 ∧ Pi * P = 1 ∧ Q * Qi = 1 ∧ Qi * Q = 1 ∧
        P * E * Q = U0 * V0 := by
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_matrix_full_rank_factorization E hRank
  obtain ⟨P, Pi, D, hPPi, hPiP, hPU, _⟩ :=
    exists_embedding_matrix_extension U U0 hU hU0
  obtain ⟨Q, Qi, W, hQQi, hQiQ, hVQ, _⟩ :=
    exists_surjection_matrix_extension V0 V hV0 hV
  refine ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, ?_⟩
  rw [← hUV, ← Matrix.mul_assoc, hPU, Matrix.mul_assoc, hVQ]

end General

section Blocks

variable {F n m p : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq m] [DecidableEq p]

/-- Rectangular rank normal form at the actual rank, including empty blocks.
No favorable pivot or preselected rank factorization is assumed. -/
theorem exists_rectangular_rank_normalization (E : Matrix (n ⊕ p) (n ⊕ m) F)
    (hRank : E.rank = Fintype.card n) :
    ∃ (P Pi : Matrix (n ⊕ p) (n ⊕ p) F)
      (Q Qi : Matrix (n ⊕ m) (n ⊕ m) F),
      P * Pi = 1 ∧ Pi * P = 1 ∧ Q * Qi = 1 ∧ Qi * Q = 1 ∧
        P * E * Q = Matrix.fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) := by
  let U0 : Matrix (n ⊕ p) n F := Matrix.fromRows 1 0
  let V0 : Matrix n (n ⊕ m) F := Matrix.fromCols 1 0
  have hU0 : Function.Injective U0.mulVec := by
    intro x y h
    funext i
    have hi := congrFun h (Sum.inl i)
    simpa [U0, Matrix.fromRows_mulVec] using hi
  have hV0 : Function.Surjective V0.mulVec := by
    intro y
    refine ⟨Sum.elim y 0, ?_⟩
    simp [V0, Matrix.fromCols_mulVec]
  obtain ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, hE⟩ :=
    matrix_rank_factor_normalize E U0 V0 hRank hU0 hV0
  refine ⟨P, Pi, Q, Qi, hP, hPi, hQ, hQi, ?_⟩
  dsimp only [U0, V0] at hE
  rw [Matrix.fromRows_mul_fromCols] at hE
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] using hE

end Blocks

end MatCP1Converse
