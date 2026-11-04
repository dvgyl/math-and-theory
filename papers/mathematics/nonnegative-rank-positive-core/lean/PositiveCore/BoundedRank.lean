module

public import MatCKronecker.NonnegativeRank
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace PositiveCore

open Matrix Module
open scoped BigOperators

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Every real matrix has a rank-sized factorization with one factor uniformly
bounded and the other bounded linearly by the largest entry of the matrix.
This includes rank zero and empty index sets. -/
theorem exists_bounded_rank_factorization (E : Matrix m n ℝ) (d : ℝ)
    (hd : 0 ≤ d) (hE : ∀ i j, |E i j| ≤ d) :
    ∃ X : Matrix m (Fin E.rank) ℝ, ∃ Y : Matrix (Fin E.rank) n ℝ,
      X * Y = E ∧ (∀ i k, |X i k| ≤ 1) ∧
      (∀ k j, |Y k j| ≤ (Fintype.card m : ℝ) * d) := by
  classical
  let f := Matrix.toEuclideanLin E
  let S := LinearMap.range f
  have hr : E.rank = finrank ℝ S := by
    exact E.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℝ).toBasis
      (EuclideanSpace.basisFun n ℝ).toBasis
  let b := (stdOrthonormalBasis ℝ S).reindex (finCongr hr.symm)
  let c (j : n) : S := ⟨f (EuclideanSpace.single j 1), LinearMap.mem_range_self _ _⟩
  have hc (j : n) (i : m) : (c j).val i = E i j := by
    simp [c, f, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  let X : Matrix m (Fin E.rank) ℝ := fun i k => (b k).val i
  let Y : Matrix (Fin E.rank) n ℝ := fun k j => inner ℝ (b k) (c j)
  have hX (i : m) (k : Fin E.rank) : |X i k| ≤ 1 := by
    have h := PiLp.norm_apply_le (b k).val i
    simpa only [X, Real.norm_eq_abs, Submodule.norm_coe, b.norm_eq_one] using h
  refine ⟨X, Y, ?_, hX, ?_⟩
  · ext i j
    change (∑ k, X i k * Y k j) = E i j
    have h := congrArg (fun x : S => x.val i) (b.sum_repr' (c j))
    simpa [X, Y, mul_comm, hc] using h
  · intro k j
    have hy : Y k j = ∑ i, X i k * E i j := by
      simp [Y, X, Submodule.coe_inner, PiLp.inner_apply, hc, mul_comm]
    rw [hy]
    calc
      |∑ i, X i k * E i j| ≤ ∑ i, |X i k * E i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : m, d := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        calc
          |X i k| * |E i j| ≤ 1 * d :=
            mul_le_mul (hX i k) (hE i j) (abs_nonneg _) (by norm_num)
          _ = d := one_mul _
      _ = (Fintype.card m : ℝ) * d := by simp

end PositiveCore
