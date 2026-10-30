module

public import MatCP1Converse.ReachableFactorization
public import MatCP1Converse.RankNormalization
public import MatCP1Converse.RankSpecialization
public import MatCP1Converse.TransformRank

@[expose] public section

noncomputable section

namespace MatCP1Converse.Pencil

open Matrix

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- A literal mixed constant-left/constant-right affine factorization whose
two factor sizes have the prescribed sum. -/
def MixedFactorizationAt (A : Pencil F m n) (r : ℕ) : Prop :=
  ∃ (a b : ℕ) (U : Matrix m (Fin a) F) (V : Matrix (Fin b) n F)
    (R0 R1 : Matrix (Fin a) n F) (L0 L1 : Matrix m (Fin b) F),
    a + b = r ∧ A.1 = U * R0 + L0 * V ∧ A.2 = U * R1 + L1 * V

omit [DecidableEq m] [DecidableEq n] in
/-- Constant row and column operations transport the actual factors. -/
theorem MixedFactorizationAt.transform {A : Pencil F m n} {r : ℕ}
    (h : MixedFactorizationAt A r) (P : Matrix m m F) (Q : Matrix n n F) :
    MixedFactorizationAt (transform P Q A) r := by
  obtain ⟨a, b, U, V, R0, R1, L0, L1, hab, h0, h1⟩ := h
  refine ⟨a, b, P * U, V * Q, R0 * Q, R1 * Q, P * L0, P * L1, hab, ?_, ?_⟩
  · change P * A.1 * Q = _
    rw [h0]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  · change P * A.2 * Q = _
    rw [h1]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Reindexing preserves both factor dimensions and the two coefficient identities. -/
theorem MixedFactorizationAt.submatrix {m' n' : Type*}
    [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
    {A : Pencil F m n} {r : ℕ} (h : MixedFactorizationAt A r)
    (em : m' ≃ m) (en : n' ≃ n) :
    MixedFactorizationAt (A.1.submatrix em en, A.2.submatrix em en) r := by
  obtain ⟨a, b, U, V, R0, R1, L0, L1, hab, h0, h1⟩ := h
  refine ⟨a, b, U.submatrix em id, V.submatrix id en,
    R0.submatrix id en, R1.submatrix id en, L0.submatrix em id,
    L1.submatrix em id, hab, ?_, ?_⟩
  · change A.1.submatrix em en = _
    rw [h0]
    change (U * R0).submatrix em en + (L0 * V).submatrix em en = _
    rw [
      Matrix.submatrix_mul _ _ em id en Function.bijective_id,
      Matrix.submatrix_mul _ _ em id en Function.bijective_id]
  · change A.2.submatrix em en = _
    rw [h1]
    change (U * R1).submatrix em en + (L1 * V).submatrix em en = _
    rw [
      Matrix.submatrix_mul _ _ em id en Function.bijective_id,
      Matrix.submatrix_mul _ _ em id en Function.bijective_id]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Undo an affine translation by translating the two affine factors. -/
theorem MixedFactorizationAt.unshift {A : Pencil F m n} {r : ℕ} (c : F)
    (h : MixedFactorizationAt (A.1 + c • A.2, A.2) r) :
    MixedFactorizationAt A r := by
  obtain ⟨a, b, U, V, R0, R1, L0, L1, hab, h0, h1⟩ := h
  change A.1 + c • A.2 = U * R0 + L0 * V at h0
  change A.2 = U * R1 + L1 * V at h1
  refine ⟨a, b, U, V, R0 - c • R1, R1, L0 - c • L1, L1, hab, ?_, h1⟩
  calc
    A.1 = (A.1 + c • A.2) - c • A.2 := by abel
    _ = (U * R0 + L0 * V) - c • (U * R1 + L1 * V) := by rw [h0, h1]
    _ = U * (R0 - c • R1) + (L0 - c • L1) * V := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
      abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Normal rank is unaffected by a bijective relabeling of row and column indices. -/
theorem normalRank_submatrix {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Pencil F m n) (em : m' ≃ m) (en : n' ≃ n) :
    normalRank (A.1.submatrix em en, A.2.submatrix em en) = A.normalRank := by
  change (A.generic.submatrix em en).rank = A.generic.rank
  exact Matrix.rank_submatrix _ _ _

section NormalizedAtZero

variable {k p q : Type*} [Fintype k] [Fintype p] [Fintype q]
  [DecidableEq k] [DecidableEq p] [DecidableEq q]

/-- A maximal-rank constant coefficient supplies the exact mixed factors.
The proof normalizes that coefficient, derives all reachable-space moments
from the genuine normal-rank bound, and then transports the factors back. -/
theorem mixedFactorizationAt_of_rank_constant
    (A : Pencil F (k ⊕ p) (k ⊕ q))
    (hRank : A.1.rank = Fintype.card k) (hNormal : A.normalRank ≤ Fintype.card k) :
    MixedFactorizationAt A (Fintype.card k) := by
  obtain ⟨P, Pi, Q, Qi, hPPi, hPiP, hQQi, hQiQ, hE⟩ :=
    exists_rectangular_rank_normalization A.1 hRank
  let E := P * A.2 * Q
  let AA := E.submatrix Sum.inl Sum.inl
  let BB := E.submatrix Sum.inl Sum.inr
  let CC := E.submatrix Sum.inr Sum.inl
  let DD := E.submatrix Sum.inr Sum.inr
  have hBlocks : Matrix.fromBlocks AA BB CC DD = E := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hPencil : rankNormalizedPencil AA BB CC DD = transform P Q A := by
    apply Prod.ext
    · exact hE.symm
    · exact hBlocks
  have hN : (rankNormalizedPencil AA BB CC DD).normalRank ≤ Fintype.card k := by
    rw [hPencil]
    exact (normalRank_transform_le P Q A).trans hNormal
  obtain ⟨a, b, U, V, R0, R1, L0, L1, hab, _, _, h0, h1⟩ :=
    normalized_pencil_mixed_factorization AA BB CC DD hN
  have hh : MixedFactorizationAt (rankNormalizedPencil AA BB CC DD) (Fintype.card k) :=
    ⟨a, b, U, V, R0, R1, L0, L1, hab, h0, h1⟩
  rw [hPencil] at hh
  have hback := hh.transform Pi Qi
  have heq : transform Pi Qi (transform P Q A) = A := by
    apply Prod.ext <;>
      simp only [transform, Matrix.mul_assoc, hQQi, Matrix.mul_one] <;>
      rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  rwa [heq] at hback

end NormalizedAtZero

/-- Every affine matrix pencil over an infinite field has a decomposition
`A(t) = U R(t) + L(t) V` with constant outer factors and affine inner factors,
and the two factor sizes sum to its actual rank over `F(t)`.
All dimensions, including zero dimensions and rank zero, are covered. -/
theorem exists_rank_mixed_factorization [Infinite F] (A : Pencil F m n) :
    ∃ (a b : ℕ) (U : Matrix m (Fin a) F) (V : Matrix (Fin b) n F)
      (R0 R1 : Matrix (Fin a) n F) (L0 L1 : Matrix m (Fin b) F),
      a + b = A.normalRank ∧ A.1 = U * R0 + L0 * V ∧ A.2 = U * R1 + L1 * V := by
  classical
  let r := A.normalRank
  have hrm : r ≤ Fintype.card m := Matrix.rank_le_card_height A.generic
  have hrn : r ≤ Fintype.card n := Matrix.rank_le_card_width A.generic
  let em : (Fin r ⊕ Fin (Fintype.card m - r)) ≃ m :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let en : (Fin r ⊕ Fin (Fintype.card n - r)) ≃ n :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  obtain ⟨c, hc⟩ := A.exists_rank_evaluation_eq
  let T : Pencil F m n := (A.1 + c • A.2, A.2)
  have hT : T.normalRank = r := by
    simpa only [coefficientChange, one_smul, zero_smul, zero_add] using
      normalRank_coefficientChange (1 : F) c 0 1 (by simp) A
  let B : Pencil F (Fin r ⊕ Fin (Fintype.card m - r))
      (Fin r ⊕ Fin (Fintype.card n - r)) :=
    (T.1.submatrix em en, T.2.submatrix em en)
  have hB0 : B.1.rank = Fintype.card (Fin r) := by
    dsimp only [B, T]
    rw [Matrix.rank_submatrix, hc, Fintype.card_fin]
  have hBN : B.normalRank ≤ Fintype.card (Fin r) := by
    dsimp only [B]
    rw [normalRank_submatrix, hT, Fintype.card_fin]
  have hB := mixedFactorizationAt_of_rank_constant B hB0 hBN
  have hTfac : MixedFactorizationAt T r := by
    have hh := hB.submatrix em.symm en.symm
    have heq : (B.1.submatrix em.symm en.symm, B.2.submatrix em.symm en.symm) = T := by
      apply Prod.ext <;> apply Matrix.ext <;> intro i j <;> simp [B, Matrix.submatrix]
    rw [heq] at hh
    simpa only [Fintype.card_fin] using hh
  exact MixedFactorizationAt.unshift c hTfac

end MatCP1Converse.Pencil
