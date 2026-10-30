import Main
import UPBRank
import SchmidtUpper
import CESTensorGeneral

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace PPTCone

/-- The local index for n+1 copies of the qutrit Tiles state. -/
def PowerIndex : ℕ → Type
  | 0 => Fin 3
  | n+1 => Fin 3 × PowerIndex n

instance powerFintype : (n : ℕ) → Fintype (PowerIndex n)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | n+1 => by
    letI := powerFintype n
    exact inferInstanceAs (Fintype (Fin 3 × PowerIndex n))

instance powerDecidableEq : (n : ℕ) → DecidableEq (PowerIndex n)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | n+1 => by
    letI := powerDecidableEq n
    exact inferInstanceAs (DecidableEq (Fin 3 × PowerIndex n))

theorem power_card (n : ℕ) : Fintype.card (PowerIndex n) = 3^(n+1) := by
  induction n with
  | zero =>
    change Fintype.card (Fin 3) = 3^(0+1)
    norm_num
  | succ n ih =>
    change Fintype.card (Fin 3 × PowerIndex n) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    exact Nat.mul_comm _ _

/-- The actual regrouped tensor power with n+1 copies of the rational Tiles projector. -/
noncomputable def tilesPower : (n : ℕ) →
    Matrix (PowerIndex n × PowerIndex n) (PowerIndex n × PowerIndex n) ℂ
  | 0 => tilesProjector
  | n+1 => tensorProduct tilesProjector (tilesPower n)

theorem tilesPower_idempotent (n : ℕ) : tilesPower n * tilesPower n = tilesPower n := by
  induction n with
  | zero => exact tilesProjector_idempotent
  | succ n ih => exact tensorProduct_idempotent _ _ tilesProjector_idempotent ih

theorem tilesPower_hermitian (n : ℕ) : (tilesPower n).IsHermitian := by
  induction n with
  | zero => exact tilesProjector_hermitian
  | succ n ih => exact tensorProduct_hermitian _ _ tilesProjector_hermitian ih

theorem tilesPower_partialTranspose (n : ℕ) : partialTranspose (tilesPower n) = tilesPower n := by
  induction n with
  | zero => exact tilesProjector_partialTranspose
  | succ n ih => exact tensorProduct_partialTranspose _ _ tilesProjector_partialTranspose ih

theorem tilesPower_nonzero (n : ℕ) : tilesPower n ≠ 0 := by
  induction n with
  | zero => exact tilesProjector_nonzero
  | succ n ih => exact tensorProduct_nonzero _ _ tilesProjector_nonzero ih

theorem tilesPower_posSemidef (n : ℕ) : (tilesPower n).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (tilesPower n)
  rw [(tilesPower_hermitian n).eq, tilesPower_idempotent] at h
  exact h

theorem tilesPower_column_hasSR (n : ℕ) :
    ∀ j, HasSR (2^(n+1)) (fun i => tilesPower n i j) := by
  induction n with
  | zero =>
    intro j
    exact tilesProjector_column_hasSR j
  | succ n ih =>
    intro j
    have h := (tilesProjector_column_hasSR (j.1.1,j.2.1)).tensor
      (ih (j.1.2,j.2.2))
    convert h using 1
    simp only [pow_succ, Nat.mul_comm]

theorem tilesPower_schmidtNumber_upper (n : ℕ) :
    PureCone (HasSR (2^(n+1))) (tilesPower n) :=
  projector_pureCone_of_columns _ _ (tilesPower_hermitian n)
    (tilesPower_idempotent n) (tilesPower_column_hasSR n)

theorem tilesPower_noSR (n : ℕ) :
    NoSR (2^(n+1)-1) (projectionSpace (tilesPower n)) := by
  induction n with
  | zero =>
    change NoSR 1 (projectionSpace tilesProjector)
    rw [projectionSpace_tilesProjector]
    exact noSR_one_of_noProduct tilesSpace tilesSpace_noProduct
  | succ n ih =>
    intro X hX hsr
    have hfixed : tensorProduct tilesProjector (tilesPower n) *ᵥ Function.uncurry X =
        Function.uncurry X := hX
    obtain ⟨hleft, hright⟩ := tensorProduct_fixed_slices tilesProjector (tilesPower n)
      tilesProjector_idempotent (tilesPower_idempotent n) (Function.uncurry X) hfixed
    have hp : 0 < 2^(n+1) := pow_pos (by decide) _
    have he : 2*(2^(n+1)-1)+1 = 2^(n+1+1)-1 := by
      rw [pow_succ]
      omega
    apply upb_tensor_no_sr tilesLeft tilesRight tiles_unextendible
      (2^(n+1)-1) (projectionSpace (tilesPower n)) ih X hright
    · apply tiles_slices_annihilate X
      simpa only [projectionSpace_tilesProjector] using hleft
    · simpa only [he] using hsr

/-- Every nonzero vector in the actual tensor-power support has the claimed
matrix rank, with the ambient bipartition explicitly regrouped by PowerIndex. -/
theorem tilesPower_support_rank_lower (n : ℕ)
    (X : Matrix (PowerIndex n) (PowerIndex n) ℂ)
    (hX : X ∈ projectionSpace (tilesPower n)) (hne : X ≠ 0) :
    2^(n+1) ≤ X.rank := by
  have hnot : ¬ X.rank ≤ 2^(n+1)-1 := by
    intro h
    exact hne (tilesPower_noSR n X hX (hasSR_of_matrix_rank_le h))
  omega

/-- The lower support-rank bound is attained, not merely a cone bound. -/
theorem tilesPower_support_minimum (n : ℕ) :
    ∃ X : Matrix (PowerIndex n) (PowerIndex n) ℂ,
      X ∈ projectionSpace (tilesPower n) ∧ X ≠ 0 ∧ X.rank = 2^(n+1) := by
  classical
  have hentry : ∃ i j, tilesPower n i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact tilesPower_nonzero n (Matrix.ext h)
  obtain ⟨i, j, hij⟩ := hentry
  let X : Matrix (PowerIndex n) (PowerIndex n) ℂ :=
    fun a b => tilesPower n (a,b) j
  have hX : X ∈ projectionSpace (tilesPower n) := by
    change tilesPower n *ᵥ Function.uncurry X = Function.uncurry X
    ext p
    exact congrFun (congrFun (tilesPower_idempotent n) p) j
  have hne : X ≠ 0 := by
    intro hz
    exact hij (congrFun (congrFun hz i.1) i.2)
  have hu : X.rank ≤ 2^(n+1) :=
    (tilesPower_column_hasSR n j).matrix_rank_le
  exact ⟨X, hX, hne, le_antisymm hu (tilesPower_support_rank_lower n X hX hne)⟩

theorem tilesPower_not_transposeConeSum (n : ℕ) :
    ¬ TransposeConeSum (HasSR (2^(n+1)-1)) (tilesPower n) := by
  let P := tilesPower n
  have hH : P.IsHermitian := tilesPower_hermitian n
  have hI : P * P = P := tilesPower_idempotent n
  have hKIdem : (1-P) * (1-P) = 1-P := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
      hI, sub_self, sub_zero]
  have hK : (1-P).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1-P)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH.eq, hKIdem] at h
    exact h
  apply not_transposeConeSum_of_separator (HasSR (2^(n+1)-1)) P (1-P) hK
  · rw [partialTranspose_sub, partialTranspose_one, tilesPower_partialTranspose]
  · simp only [sub_mul, Matrix.one_mul, hI, sub_self, Matrix.trace_zero]
  · exact tilesPower_nonzero n
  · intro v hv hzero
    have hfixed : P *ᵥ v = v := by
      have hz : v - P *ᵥ v = 0 := by
        simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hzero
      exact (sub_eq_zero.mp hz).symm
    have hm : (fun a b => v (a,b)) ∈ projectionSpace (tilesPower n) := hfixed
    have hz := tilesPower_noSR n (fun a b => v (a,b)) hm hv
    ext p
    exact congrFun (congrFun hz p.1) p.2

theorem PureCone.zero {A B : Type*} (V : (A × B → ℂ) → Prop) :
    PureCone V (0 : Matrix (A × B) (A × B) ℂ) := by
  refine ⟨0, Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp

theorem PureCone.to_transposeConeSum {A B : Type*}
    {V : (A × B → ℂ) → Prop} {R : Matrix (A × B) (A × B) ℂ}
    (h : PureCone V R) : TransposeConeSum V R := by
  exact ⟨R, 0, h, PureCone.zero V, by simp only [partialTranspose_zero, add_zero]⟩

/-- The exact Schmidt number: membership in the true pure-state cone is
equivalent to allowing at least 2^(n+1) simple tensors per vector. -/
theorem tilesPower_schmidtNumber_exact (n k : ℕ) :
    PureCone (HasSR k) (tilesPower n) ↔ 2^(n+1) ≤ k := by
  constructor
  · intro h
    by_contra hk
    have hkle : k ≤ 2^(n+1)-1 := by omega
    exact tilesPower_not_transposeConeSum n
      ((h.mono (fun _ hv => hv.mono hkle)).to_transposeConeSum)
  · intro hk
    exact (tilesPower_schmidtNumber_upper n).mono (fun _ hv => hv.mono hk)

/-- An unconditional explicit PPT family with exact Schmidt numbers and
a strictly stronger transpose-cone exclusion at the same threshold. -/
theorem sharp_tiles_power_family (n : ℕ) :
    tilesPower n ≠ 0 ∧ (tilesPower n).PosSemidef ∧
      (partialTranspose (tilesPower n)).PosSemidef ∧
      (∀ k, PureCone (HasSR k) (tilesPower n) ↔ 2^(n+1) ≤ k) ∧
      ¬ TransposeConeSum (HasSR (2^(n+1)-1)) (tilesPower n) := by
  exact ⟨tilesPower_nonzero n, tilesPower_posSemidef n,
    (tilesPower_partialTranspose n).symm ▸ tilesPower_posSemidef n,
    tilesPower_schmidtNumber_exact n, tilesPower_not_transposeConeSum n⟩

#print axioms upb_tensor_no_sr
#print axioms tilesPower_schmidtNumber_exact
#print axioms tilesPower_support_minimum
#print axioms sharp_tiles_power_family

end PPTCone
