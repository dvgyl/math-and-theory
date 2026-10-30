import CESTensor
import TilesTensor
import ConeExclusion

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace PPTCone

theorem tilesTensor_no_sr2 (v : I9 × I9 → ℂ)
    (hv : HasSR2 v) (hfixed : tilesTensor *ᵥ v = v) : v = 0 := by
  obtain ⟨hleft, hright⟩ := tilesTensor_fixed_slices v hfixed
  exact tensor_no_sr2 tilesSpace tilesSpace tilesSpace_noProduct
    tilesSpace_noProduct v hleft hright hv

theorem partialTranspose_one {A B : Type*} [DecidableEq A] [DecidableEq B] :
    partialTranspose (1 : Matrix (A × B) (A × B) ℂ) = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases hac : a = c <;> by_cases hbd : b = d <;>
    simp [partialTranspose, Matrix.one_apply, Prod.mk.injEq, hac, hbd, eq_comm]

theorem tilesTensor_complement_idempotent :
    (1 - tilesTensor) * (1 - tilesTensor) = 1 - tilesTensor := by
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    tilesTensor_idempotent, sub_self, sub_zero]

theorem tilesTensor_complement_posSemidef : (1 - tilesTensor).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - tilesTensor)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    tilesTensor_hermitian.eq, tilesTensor_complement_idempotent] at h
  exact h

/-- The explicit rational Tiles tensor projector lies outside
SN₂ + partialTranspose(SN₂). -/
theorem tilesTensor_not_isDSP2 : ¬ IsDSP2 tilesTensor := by
  apply not_isDSP2_of_separator tilesTensor (1 - tilesTensor)
    tilesTensor_complement_posSemidef
  · rw [partialTranspose_sub, partialTranspose_one, tilesTensor_partialTranspose]
  · simp only [sub_mul, Matrix.one_mul, tilesTensor_idempotent,
      sub_self, Matrix.trace_zero]
  · exact tilesTensor_nonzero
  · intro v hv hzero
    apply tilesTensor_no_sr2 v hv
    have hz : v - tilesTensor *ᵥ v = 0 := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hzero
    exact (sub_eq_zero.mp hz).symm

/-- The central, unconditional matrix-cone counterexample: the stated explicit
81-by-81 complex matrix is nonzero, positive semidefinite, has positive partial
transpose, and admits no decomposition into a Schmidt-number-two positive
matrix plus the partial transpose of another such matrix. -/
theorem explicit_ppt_counterexample :
    tilesTensor ≠ 0 ∧ tilesTensor.PosSemidef ∧
      (partialTranspose tilesTensor).PosSemidef ∧ ¬ IsDSP2 tilesTensor := by
  exact ⟨tilesTensor_nonzero, tilesTensor_posSemidef,
    tilesTensor_partialTranspose.symm ▸ tilesTensor_posSemidef,
    tilesTensor_not_isDSP2⟩

/-- In particular, the PPT cone on a 9-by-9 bipartite system is not contained
in SN₂ + partialTranspose(SN₂). -/
theorem ppt_not_subset_dsp2 :
    ¬ (∀ R : Matrix (I9 × I9) (I9 × I9) ℂ,
      R.PosSemidef → (partialTranspose R).PosSemidef → IsDSP2 R) := by
  intro h
  exact tilesTensor_not_isDSP2 (h tilesTensor tilesTensor_posSemidef
    (tilesTensor_partialTranspose.symm ▸ tilesTensor_posSemidef))

#print axioms explicit_ppt_counterexample
#print axioms ppt_not_subset_dsp2

end PPTCone
