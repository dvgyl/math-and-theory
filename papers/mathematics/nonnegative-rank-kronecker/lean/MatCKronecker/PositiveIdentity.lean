module

public import MatCKronecker.NonnegativeRank

@[expose] public section

namespace MatCKronecker

open Matrix

def onesMatrix (n : Type*) : Matrix n n ℝ := fun _ _ => 1

/-- The matrix `J + rho I`, with its literal entries exposed. -/
def nearOne (n : Type*) [DecidableEq n] (rho : ℝ) : Matrix n n ℝ :=
  fun i j => 1 + if i = j then rho else 0

theorem nearOne_eq (n : Type*) [DecidableEq n] (rho : ℝ) :
    nearOne n rho = rho • (1 : Matrix n n ℝ) + onesMatrix n := by
  ext i j
  by_cases h : i = j <;> simp [nearOne, onesMatrix, h, add_comm]

theorem nearOne_nonneg (n : Type*) [DecidableEq n] {rho : ℝ} (hrho : 0 ≤ rho) :
    EntryNonneg (nearOne n rho) := by
  intro i j
  by_cases h : i = j <;> simp [nearOne, h]
  positivity

theorem onesMatrix_mul (n : Type*) [Fintype n] :
    onesMatrix n * onesMatrix n = (Fintype.card n : ℝ) • onesMatrix n := by
  ext i j
  simp [Matrix.mul_apply, onesMatrix]

/-- Explicit inverse formula, used below only through its proved product identity. -/
noncomputable def nearOneInverse (n : Type*) [Fintype n] [DecidableEq n] (rho : ℝ) : Matrix n n ℝ :=
  rho⁻¹ • (1 : Matrix n n ℝ) -
    (rho * (rho + (Fintype.card n : ℝ)))⁻¹ • onesMatrix n

theorem nearOneInverse_mul (n : Type*) [Fintype n] [DecidableEq n]
    {rho : ℝ} (hrho : 0 < rho) :
    nearOneInverse n rho * nearOne n rho = 1 := by
  have hρ : rho ≠ 0 := ne_of_gt hrho
  have hN : rho + (Fintype.card n : ℝ) ≠ 0 := by positivity
  rw [nearOne_eq]
  ext i j
  simp [nearOneInverse, sub_mul, mul_add, smul_smul, onesMatrix_mul, onesMatrix]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
  all_goals field_simp
  all_goals ring

theorem rank_nearOne (n : Type*) [Fintype n] [DecidableEq n]
    {rho : ℝ} (hrho : 0 < rho) : (nearOne n rho).rank = Fintype.card n := by
  apply le_antisymm (Matrix.rank_le_card_width _)
  have h := Matrix.rank_mul_le_right (nearOneInverse n rho) (nearOne n rho)
  simpa only [nearOneInverse_mul n hrho, Matrix.rank_one] using h

theorem nnrank_nearOne (n : Type*) [Fintype n] [DecidableEq n]
    {rho : ℝ} (hrho : 0 < rho) : nnrank (nearOne n rho) = Fintype.card n := by
  apply le_antisymm (nnrank_le_card_width (nearOne_nonneg n hrho.le))
  simpa only [rank_nearOne n hrho] using rank_le_nnrank (nearOne_nonneg n hrho.le)

end MatCKronecker
