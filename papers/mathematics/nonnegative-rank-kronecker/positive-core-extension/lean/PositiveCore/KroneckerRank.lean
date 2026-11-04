module

public import PositiveCore.BoundedRank
public import PositiveCore.RankSaturation
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

namespace PositiveCore

open Matrix
open scoped BigOperators Kronecker

/-- A finite real matrix has an ordinary rank factorization, including rank
zero. This corollary removes the entrywise bound from the quantitative lemma. -/
theorem exists_rank_factorization {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    ∃ X : Matrix m (Fin A.rank) ℝ, ∃ Y : Matrix (Fin A.rank) n ℝ, X * Y = A := by
  classical
  let d : ℝ := ∑ i, ∑ j, |A i j|
  have hd : 0 ≤ d :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ i j, |A i j| ≤ d := by
    intro i j
    have hj : |A i j| ≤ ∑ j, |A i j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (Finset.mem_univ j)
    have hi : (∑ j, |A i j|) ≤ d :=
      Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (A i j)) (Finset.mem_univ i)
    exact hj.trans hi
  obtain ⟨X, Y, hXY, _, _⟩ := exists_bounded_rank_factorization A d hd hbound
  exact ⟨X, Y, hXY⟩

/-- Ordinary real matrix rank is multiplicative under Kronecker products.
The proof factors both matrices at their ordinary ranks and tensors their
proved left and right inverses; no nonnegative-rank assertion is used. -/
theorem rank_kronecker {m n a b : Type*}
    [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    (A : Matrix m n ℝ) (B : Matrix a b ℝ) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  obtain ⟨X, Y, hXY⟩ := exists_rank_factorization A
  obtain ⟨Z, T, hZT⟩ := exists_rank_factorization B
  have hXyr : (X * Y).rank = Fintype.card (Fin A.rank) := by simp [hXY]
  have hZtr : (Z * T).rank = Fintype.card (Fin B.rank) := by simp [hZT]
  have hXr := (saturated_factor_ranks X Y hXyr).1
  have hYr := (saturated_factor_ranks X Y hXyr).2
  have hZr := (saturated_factor_ranks Z T hZtr).1
  have hTr := (saturated_factor_ranks Z T hZtr).2
  obtain ⟨XL, hXL⟩ := exists_left_inverse_of_full_column_rank X hXr
  obtain ⟨YR, hYR⟩ := exists_right_inverse_of_full_row_rank Y hYr
  obtain ⟨ZL, hZL⟩ := exists_left_inverse_of_full_column_rank Z hZr
  obtain ⟨TR, hTR⟩ := exists_right_inverse_of_full_row_rank T hTr
  have hprod : (X ⊗ₖ Z) * (Y ⊗ₖ T) = A ⊗ₖ B := by
    rw [← Matrix.mul_kronecker_mul, hXY, hZT]
  have hAI : XL * A * YR = 1 := by
    calc
      XL * A * YR = XL * (X * Y) * YR :=
        congrArg (fun M : Matrix m n ℝ => XL * M * YR) hXY.symm
      _ = 1 := by rw [← Matrix.mul_assoc XL X Y, hXL, Matrix.one_mul, hYR]
  have hBI : ZL * B * TR = 1 := by
    calc
      ZL * B * TR = ZL * (Z * T) * TR :=
        congrArg (fun M : Matrix a b ℝ => ZL * M * TR) hZT.symm
      _ = 1 := by rw [← Matrix.mul_assoc ZL Z T, hZL, Matrix.one_mul, hTR]
  have hId : (XL ⊗ₖ ZL) * (A ⊗ₖ B) * (YR ⊗ₖ TR) = 1 := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hAI, hBI, Matrix.one_kronecker_one]
  apply le_antisymm
  · calc
      (A ⊗ₖ B).rank = ((X ⊗ₖ Z) * (Y ⊗ₖ T)).rank := congrArg Matrix.rank hprod.symm
      _ ≤ (X ⊗ₖ Z).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin A.rank × Fin B.rank) := Matrix.rank_le_card_width _
      _ = A.rank * B.rank := by simp
  · have h := (Matrix.rank_mul_le_left ((XL ⊗ₖ ZL) * (A ⊗ₖ B)) (YR ⊗ₖ TR)).trans
      (Matrix.rank_mul_le_right (XL ⊗ₖ ZL) (A ⊗ₖ B))
    rw [hId, Matrix.rank_one] at h
    simpa using h

end PositiveCore
