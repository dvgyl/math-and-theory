import GeneralDefs
import Mathlib.Data.Matrix.Rank

open scoped BigOperators Matrix

namespace PPTCone

theorem HasSR.matrix_rank_le {A B : Type*} [Fintype A] [Fintype B]
    {k : ℕ} {M : Matrix A B ℂ}
    (h : HasSR k (Function.uncurry M)) : M.rank ≤ k := by
  classical
  obtain ⟨r, hr, a, b, hab⟩ := h
  let U : Matrix A (Fin r) ℂ := fun i t => a t i
  let V : Matrix (Fin r) B ℂ := fun t j => b t j
  have he : M = U * V := by
    ext i j
    exact hab i j
  rw [he]
  exact (Matrix.rank_mul_le_left U V).trans
    ((Matrix.rank_le_card_width U).trans (by simpa using hr))

theorem hasSR_of_matrix_rank_le {A B : Type*} [Fintype A] [Fintype B]
    {k : ℕ} {M : Matrix A B ℂ} (h : M.rank ≤ k) :
    HasSR k (Function.uncurry M) := by
  classical
  let W := LinearMap.range M.mulVecLin
  let β := Module.finBasis ℂ W
  let col : B → W := fun j =>
    ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨M.rank, h, (fun t i => (β t : A → ℂ) i),
    (fun t j => β.repr (col j) t), ?_⟩
  intro i j
  have he := congrArg (fun w : W => (w : A → ℂ) i) (β.sum_repr (col j))
  have hc : (col j : A → ℂ) i = M i j := by
    simp only [col, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.transpose_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at he
  rw [hc] at he
  simpa only [Function.uncurry_apply_pair, mul_comm] using he.symm

theorem hasSR_iff_matrix_rank_le {A B : Type*} [Fintype A] [Fintype B]
    (k : ℕ) (M : Matrix A B ℂ) :
    HasSR k (Function.uncurry M) ↔ M.rank ≤ k :=
  ⟨HasSR.matrix_rank_le, hasSR_of_matrix_rank_le⟩

end PPTCone
