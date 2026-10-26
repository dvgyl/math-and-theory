module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! An exact bridge from positive definiteness to the spectral parameter bound. -/
@[expose] public section

namespace MathAndTheory.DomiRank
open Matrix

/-- If I+sA is positive definite, then s is below the negative reciprocal
of every negative real eigenvalue of A. In particular this applies to the
smallest eigenvalue of a real symmetric adjacency matrix. -/
theorem parameter_lt_neg_inv_eigenvalue
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} {s lam : ℝ} {v : n → ℝ}
    (hpd : ((1 : Matrix n n ℝ) + s • M).PosDef)
    (hlam : lam < 0) (hv : v ≠ 0) (heig : M *ᵥ v = lam • v) :
    s < -1 / lam := by
  have hquad := hpd.dotProduct_mulVec_pos hv
  have hnorm : 0 ≤ v ⬝ᵥ v := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    heig, star_trivial, dotProduct_add, dotProduct_smul, smul_eq_mul] at hquad
  have hcoeff : 0 < 1 + s * lam := by
    nlinarith
  exact (lt_div_iff_of_neg hlam).2 (by linarith)

end MathAndTheory.DomiRank
