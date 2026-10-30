module

public import MatCP1Converse.StaticFactor
public import MatCP1Converse.Pencil
public import MatCP1Converse.CompressionCoordinates

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n m p a b : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p] [Fintype a] [Fintype b]
  [DecidableEq n]

omit [Fintype a] in
/-- The full static-compression estimate with actual constant coordinate changes.
The normal rank is computed over `RatFunc F`, and the bound is the rank over `F` of
the entire bordered difference. The required extension maps are constructed here. -/
theorem exists_static_compression_rank_bound
    (A0 A1 : Matrix n n F) (X0 X1 : Matrix n m F) (Y0 Y1 : Matrix p n F)
    (hX0 : Function.Injective X0.mulVec) (hX1 : Function.Injective X1.mulVec)
    (hY0 : Function.Surjective Y0.mulVec) (hY1 : Function.Surjective Y1.mulVec)
    (Q : Matrix a n F) (K : Matrix n b F) :
    ∃ S Sinv T Tinv : Matrix n n F,
      S * Sinv = 1 ∧ Sinv * S = 1 ∧ T * Tinv = 1 ∧ Tinv * T = 1 ∧
      S * X0 = X1 ∧ Y1 * T = Y0 ∧
      Pencil.normalRank
        ((Q * Sinv * A1 * T * K, Q * Sinv * T * K) - (Q * A0 * K, Q * K)) ≤
        (fromBlocks (A1 - A0) (X1 - X0) (Y1 - Y0) (0 : Matrix p m F)).rank := by
  obtain ⟨S, Sinv, D, hSright, hSleft, hSX, hSD⟩ :=
    exists_embedding_matrix_extension X0 X1 hX0 hX1
  obtain ⟨T, Tinv, W, hTright, hTleft, hYT, hTW⟩ :=
    exists_surjection_matrix_extension Y0 Y1 hY0 hY1
  refine ⟨S, Sinv, T, Tinv, hSright, hSleft, hTright, hTleft, hSX, hYT, ?_⟩
  have hc1 : Pencil.const (1 : Matrix n n F) = 1 := by
    ext i j
    simp [Pencil.const, Matrix.one_apply]
  have hSD' : Pencil.const S - 1 = Pencil.const (X1 - X0) * Pencil.const D := by
    simpa only [Pencil.const_sub, Pencil.const_mul, hc1] using congrArg Pencil.const hSD
  have hTW' : Pencil.const T - 1 = Pencil.const W * Pencil.const (Y1 - Y0) := by
    simpa only [Pencil.const_sub, Pencil.const_mul, hc1] using congrArg Pencil.const hTW
  have hSinv : Pencil.const Sinv * Pencil.const S = 1 := by
    simpa only [Pencil.const_mul, hc1] using congrArg Pencil.const hSleft
  let M0 := Pencil.const A0 + (RatFunc.X : RatFunc F) • (1 : Matrix n n (RatFunc F))
  let M1 := Pencil.const A1 + (RatFunc.X : RatFunc F) • (1 : Matrix n n (RatFunc F))
  have hg0 : Pencil.generic (Q * A0 * K, Q * K) = Pencil.const Q * M0 * Pencil.const K := by
    simp [Pencil.generic, M0, Pencil.const_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hg1 : Pencil.generic (Q * Sinv * A1 * T * K, Q * Sinv * T * K) =
      Pencil.const Q * Pencil.const Sinv * M1 * Pencil.const T * Pencil.const K := by
    simp [Pencil.generic, M1, Pencil.const_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hg : Pencil.generic
      ((Q * Sinv * A1 * T * K, Q * Sinv * T * K) - (Q * A0 * K, Q * K)) =
      Pencil.const Q * Pencil.const Sinv * (M1 * Pencil.const T - Pencil.const S * M0) *
        Pencil.const K := by
    rw [Pencil.generic_sub, hg1, hg0]
    exact compression_difference_identity (Pencil.const Q) (Pencil.const K)
      M0 M1 (Pencil.const S) (Pencil.const Sinv) (Pencil.const T) hSinv
  have hb : fromBlocks (Pencil.const A1 - Pencil.const A0)
      (Pencil.const (X1 - X0)) (Pencil.const (Y1 - Y0)) (0 : Matrix p m (RatFunc F)) =
      Pencil.const (fromBlocks (A1 - A0) (X1 - X0) (Y1 - Y0) (0 : Matrix p m F)) := by
    ext i j
    cases i <;> cases j <;> simp [Pencil.const, fromBlocks]
  have hmiddle : (M1 * Pencil.const T - Pencil.const S * M0).rank ≤
      (fromBlocks (A1 - A0) (X1 - X0) (Y1 - Y0) (0 : Matrix p m F)).rank := by
    have h := static_shift_rank_le (Pencil.const A0) (Pencil.const A1)
      (Pencil.const S) (Pencil.const T) (Pencil.const (X1 - X0))
      (Pencil.const (Y1 - Y0)) (Pencil.const D) (Pencil.const W) RatFunc.X hSD' hTW'
    rw [hb] at h
    exact h.trans (Pencil.const_rank_le _)
  unfold Pencil.normalRank
  rw [hg]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans hmiddle)

/-- Actual static compressions with valid quotient and kernel bases satisfy the
bordered-difference normal-rank bound. The new bases are produced, with their full
ranks and exact kernel/image proved, rather than assumed. -/
theorem exists_valid_static_compression_bound
    (A0 A1 : Matrix n n F) (X0 X1 : Matrix n m F) (Y0 Y1 : Matrix p n F)
    (hX0 : Function.Injective X0.mulVec) (hX1 : Function.Injective X1.mulVec)
    (hY0 : Function.Surjective Y0.mulVec) (hY1 : Function.Surjective Y1.mulVec)
    (Q0 : Matrix a n F) (K0 : Matrix n b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hK0 : Function.Injective K0.mulVec)
    (hker0 : LinearMap.ker Q0.mulVecLin = LinearMap.range X0.mulVecLin)
    (hrange0 : LinearMap.range K0.mulVecLin = LinearMap.ker Y0.mulVecLin) :
    ∃ (Q1 : Matrix a n F) (K1 : Matrix n b F),
      Function.Surjective Q1.mulVec ∧ Function.Injective K1.mulVec ∧
      LinearMap.ker Q1.mulVecLin = LinearMap.range X1.mulVecLin ∧
      LinearMap.range K1.mulVecLin = LinearMap.ker Y1.mulVecLin ∧
      Pencil.normalRank ((Q1 * A1 * K1, Q1 * K1) - (Q0 * A0 * K0, Q0 * K0)) ≤
        (fromBlocks (A1 - A0) (X1 - X0) (Y1 - Y0) (0 : Matrix p m F)).rank := by
  obtain ⟨S, Sinv, T, Tinv, hSright, hSleft, hTright, hTleft, hSX, hYT, hRank⟩ :=
    exists_static_compression_rank_bound A0 A1 X0 X1 Y0 Y1 hX0 hX1 hY0 hY1 Q0 K0
  obtain ⟨hQ1, hK1, hker1, hrange1⟩ := matrix_transport_quotient_kernel
    X0 X1 Y0 Y1 Q0 K0 S Sinv T Tinv hSleft hSright hTleft hTright hSX hYT
    hQ0 hK0 hker0 hrange0
  refine ⟨Q0 * Sinv, T * K0, hQ1, hK1, hker1, hrange1, ?_⟩
  simpa only [Matrix.mul_assoc] using hRank

end MatCP1Converse
