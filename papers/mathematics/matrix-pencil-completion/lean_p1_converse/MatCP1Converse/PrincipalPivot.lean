module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

/-- The rank-`n` block matrix determined by an invertible leading block. -/
def completedBlock (G Ginv : Matrix n n F) (B : Matrix n m F)
    (C : Matrix p n F) : Matrix (n ⊕ p) (n ⊕ m) F :=
  fromBlocks G B C (C * Ginv * B)

/-- Its principal pivot transform has an actual zero lower-right block. -/
def principalPivot (Ginv : Matrix n n F) (B : Matrix n m F)
    (C : Matrix p n F) : Matrix (n ⊕ p) (n ⊕ m) F :=
  fromBlocks Ginv (-(Ginv * B)) (C * Ginv) 0

omit [Fintype m] [DecidableEq m] in
theorem pivot_left_product
    (G Ginv : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hleft : Ginv * G = 1) :
    fromBlocks (-Ginv) 0 (-(C * Ginv)) (1 : Matrix p p F) *
      completedBlock G Ginv B C =
      fromBlocks (-1 : Matrix n n F) (-(Ginv * B)) 0 (0 : Matrix p m F) := by
  unfold completedBlock
  rw [fromBlocks_multiply]
  congr 1
  · simp [hleft]
  · simp
  · simp [Matrix.mul_assoc, hleft]
  · simp

omit [Fintype p] [DecidableEq p] in
theorem pivot_right_product
    (G Ginv : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hright : G * Ginv = 1) :
    completedBlock G Ginv B C *
      fromBlocks Ginv (-(Ginv * B)) 0 (1 : Matrix m m F) =
      fromBlocks (1 : Matrix n n F) 0 (C * Ginv) (0 : Matrix p m F) := by
  unfold completedBlock
  rw [fromBlocks_multiply]
  congr 1
  · simp [hright]
  · simp [← Matrix.mul_assoc, hright]
  · simp
  · simp [Matrix.mul_assoc]

/-- The exact difference factorization uses constant invertible outside matrices. -/
theorem principalPivot_sub_factorization
    (G0 G0inv G1 G1inv : Matrix n n F)
    (B0 B1 : Matrix n m F) (C0 C1 : Matrix p n F)
    (h0 : G0 * G0inv = 1) (h1 : G1inv * G1 = 1) :
    principalPivot G1inv B1 C1 - principalPivot G0inv B0 C0 =
      fromBlocks (-G1inv) 0 (-(C1 * G1inv)) (1 : Matrix p p F) *
        (completedBlock G1 G1inv B1 C1 - completedBlock G0 G0inv B0 C0) *
        fromBlocks G0inv (-(G0inv * B0)) 0 (1 : Matrix m m F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, pivot_left_product G1 G1inv B1 C1 h1,
    Matrix.mul_assoc, pivot_right_product G0 G0inv B0 C0 h0,
    fromBlocks_multiply, fromBlocks_multiply]
  unfold principalPivot
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, Matrix.neg_mul, Matrix.mul_neg] <;> abel

/-- Principal pivoting is an exact rank isometry between two such block matrices.
All inverses are witnessed by matrix identities, including the empty pivot block. -/
theorem principalPivot_sub_rank
    (G0 G0inv G1 G1inv : Matrix n n F)
    (B0 B1 : Matrix n m F) (C0 C1 : Matrix p n F)
    (h0left : G0inv * G0 = 1) (h0right : G0 * G0inv = 1)
    (h1left : G1inv * G1 = 1) (h1right : G1 * G1inv = 1) :
    (principalPivot G1inv B1 C1 - principalPivot G0inv B0 C0).rank =
      (completedBlock G1 G1inv B1 C1 - completedBlock G0 G0inv B0 C0).rank := by
  let L : Matrix (n ⊕ p) (n ⊕ p) F :=
    fromBlocks (-G1inv) 0 (-(C1 * G1inv)) 1
  let Linv : Matrix (n ⊕ p) (n ⊕ p) F := fromBlocks (-G1) 0 (-C1) 1
  let R : Matrix (n ⊕ m) (n ⊕ m) F := fromBlocks G0inv (-(G0inv * B0)) 0 1
  let Rinv : Matrix (n ⊕ m) (n ⊕ m) F := fromBlocks G0 B0 0 1
  let D := completedBlock G1 G1inv B1 C1 - completedBlock G0 G0inv B0 C0
  have hL : Linv * L = 1 := by
    dsimp [Linv, L]
    rw [fromBlocks_multiply]
    simp [h1right]
  have hR : R * Rinv = 1 := by
    dsimp [R, Rinv]
    rw [fromBlocks_multiply]
    simp [h0left]
  have hfactor : principalPivot G1inv B1 C1 - principalPivot G0inv B0 C0 =
      L * D * R := principalPivot_sub_factorization G0 G0inv G1 G1inv
        B0 B1 C0 C1 h0right h1left
  rw [hfactor]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hrecover : Linv * (L * D * R) * Rinv = D := by
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul]
      rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    calc
      D.rank = (Linv * (L * D * R) * Rinv).rank := congrArg Matrix.rank hrecover.symm
      _ ≤ (L * D * R).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end MatCP1Converse
