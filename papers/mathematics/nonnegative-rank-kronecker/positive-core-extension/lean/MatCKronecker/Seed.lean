module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MatCKronecker

open Matrix

def seed : Matrix (Fin 4) (Fin 4) ℝ :=
  !![17, 17, 1, 1; 1, 17, 17, 1; 1, 1, 17, 17; 17, 1, 1, 17]

noncomputable def seedLeft : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then 37 / 36 else 1 / 36

noncomputable def seedRight : Matrix (Fin 4) (Fin 4) ℝ :=
  !![161/10, 161/10, 1/10, 1/10;
     1/10, 161/10, 161/10, 1/10;
     1/10, 1/10, 161/10, 161/10;
     161/10, 1/10, 1/10, 161/10]

def seedRankLeft : Matrix (Fin 4) (Fin 3) ℝ :=
  !![17, 17, 1; 1, 17, 17; 1, 1, 17; 17, 1, 1]

def seedRankRight : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 0, -1; 0, 0, 1, 1]

theorem seed_positive (i j : Fin 4) : 0 < seed i j := by
  fin_cases i <;> fin_cases j <;> norm_num [seed]

theorem seedLeft_lower (i j : Fin 4) : (1 : ℝ) / 36 ≤ seedLeft i j := by
  simp only [seedLeft]
  split <;> norm_num

theorem seedRight_lower (i j : Fin 4) : (1 : ℝ) / 10 ≤ seedRight i j := by
  fin_cases i <;> fin_cases j <;> norm_num [seedRight]

theorem seed_nonnegative_factorization : seedLeft * seedRight = seed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedLeft, seedRight, seed, Matrix.mul_apply, Fin.sum_univ_succ]

theorem seed_rank_factorization : seedRankLeft * seedRankRight = seed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedRankLeft, seedRankRight, seed, Matrix.mul_apply, Fin.sum_univ_succ]

theorem seedRankLeft_abs_le (i : Fin 4) (j : Fin 3) :
    |seedRankLeft i j| ≤ 17 := by
  fin_cases i <;> fin_cases j <;> norm_num [seedRankLeft]

theorem seedRankRight_abs_le (i : Fin 3) (j : Fin 4) :
    |seedRankRight i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [seedRankRight]

theorem seed_diagonal (i : Fin 4) : seed i i = 17 := by
  fin_cases i <;> norm_num [seed]

theorem seed_cross_product (i j : Fin 4) (h : i ≠ j) :
    seed i j * seed j i ≤ 17 := by
  fin_cases i <;> fin_cases j <;> norm_num [seed] at *

def seedMinor : Matrix (Fin 3) (Fin 3) ℝ :=
  seed.submatrix Fin.castSucc Fin.castSucc

theorem seedMinor_det : seedMinor.det = 4608 := by
  norm_num [seedMinor, seed, Matrix.det_fin_three, Matrix.submatrix]

theorem seed_rank : seed.rank = 3 := by
  apply le_antisymm
  · rw [← seed_rank_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have hm : seedMinor.rank = 3 := by
      have hd : seedMinor.det ≠ 0 := by rw [seedMinor_det]; norm_num
      simpa using Matrix.rank_of_det_ne_zero hd
    rw [← hm]
    exact Matrix.rank_submatrix_le seed Fin.castSucc Fin.castSucc

end MatCKronecker
