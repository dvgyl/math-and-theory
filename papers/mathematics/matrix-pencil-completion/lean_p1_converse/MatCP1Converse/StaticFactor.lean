module

public import MatCP1Converse.MatrixExtension
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n m p a b : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p] [Fintype a] [Fintype b]
  [DecidableEq n]

/-- The aligned difference is a rectangular compression of the bordered difference.
This identity bypasses any decomposition into intermediate perturbations. -/
theorem static_displacement_factorization
    (M0 M1 S T : Matrix n n F) (DX : Matrix n m F) (DY : Matrix p n F)
    (D : Matrix m n F) (W : Matrix n p F)
    (hS : S - 1 = DX * D) (hT : T - 1 = W * DY) :
    M1 * T - S * M0 =
      fromCols (1 : Matrix n n F) (M1 * W) * fromBlocks (M1 - M0) DX DY 0 *
        fromRows (1 : Matrix n n F) (-(D * M0)) := by
  have hS' : S = DX * D + 1 := sub_eq_iff_eq_add.mp hS
  have hT' : T = W * DY + 1 := sub_eq_iff_eq_add.mp hT
  rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows, hS', hT']
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, add_zero, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- Common scalar shifts disappear from the central bordered matrix. -/
theorem static_shift_factorization
    (A0 A1 S T : Matrix n n F) (DX : Matrix n m F) (DY : Matrix p n F)
    (D : Matrix m n F) (W : Matrix n p F) (z : F)
    (hS : S - 1 = DX * D) (hT : T - 1 = W * DY) :
    (A1 + z • 1) * T - S * (A0 + z • 1) =
      fromCols (1 : Matrix n n F) ((A1 + z • 1) * W) * fromBlocks (A1 - A0) DX DY 0 *
        fromRows (1 : Matrix n n F) (-(D * (A0 + z • 1))) := by
  have hd : (A1 + z • 1) - (A0 + z • 1) = A1 - A0 := by abel
  exact (static_displacement_factorization
    (A0 + z • 1) (A1 + z • 1) S T DX DY D W hS hT).trans
    (congrArg (fun M : Matrix n n F =>
      fromCols (1 : Matrix n n F) ((A1 + z • 1) * W) * fromBlocks M DX DY 0 *
        fromRows (1 : Matrix n n F) (-(D * (A0 + z • 1)))) hd)

omit [Fintype a] [Fintype b] in
/-- Insert the inverse coordinate change into the actual compressed difference. -/
theorem compression_difference_identity
    (Q : Matrix a n F) (K : Matrix n b F) (M0 M1 S Sinv T : Matrix n n F)
    (hSinv : Sinv * S = 1) :
    Q * Sinv * M1 * T * K - Q * M0 * K =
      Q * Sinv * (M1 * T - S * M0) * K := by
  have hh : Sinv * (M1 * T - S * M0) = Sinv * M1 * T - M0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc Sinv S M0, hSinv, Matrix.one_mul,
      ← Matrix.mul_assoc Sinv M1 T]
  calc
    _ = Q * (Sinv * M1 * T - M0) * K := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = Q * (Sinv * (M1 * T - S * M0)) * K := by rw [hh]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The exact static factorization contracts matrix rank. -/
theorem static_shift_rank_le
    (A0 A1 S T : Matrix n n F) (DX : Matrix n m F) (DY : Matrix p n F)
    (D : Matrix m n F) (W : Matrix n p F) (z : F)
    (hS : S - 1 = DX * D) (hT : T - 1 = W * DY) :
    ((A1 + z • 1) * T - S * (A0 + z • 1)).rank ≤
      (fromBlocks (A1 - A0) DX DY (0 : Matrix p m F)).rank := by
  rw [static_shift_factorization A0 A1 S T DX DY D W z hS hT]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end MatCP1Converse
