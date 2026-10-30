import Main
import Hierarchy
import CESTensorGeneral
import GenericCone

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace PPTCone

theorem hierarchyProjector_noSR (n : ℕ) :
    NoSR (n+1) (projectionSpace (hierarchyProjector n)) := by
  induction n with
  | zero =>
    change NoSR 1 (projectionSpace tilesProjector)
    rw [projectionSpace_tilesProjector]
    exact noSR_one_of_noProduct tilesSpace tilesSpace_noProduct
  | succ n ih =>
    intro X hX hsr
    have hfixed : tensorSquare (hierarchyProjector n) *ᵥ Function.uncurry X =
        Function.uncurry X := hX
    obtain ⟨hleft, hright⟩ := tensorSquare_fixed_slices (hierarchyProjector n)
      (hierarchyProjector_idempotent n) (Function.uncurry X) hfixed
    have hz := tensor_no_sr (n+1) (Nat.succ_le_succ (Nat.zero_le n))
      (projectionSpace (hierarchyProjector n)) (projectionSpace (hierarchyProjector n))
      ih ih (Function.uncurry X) hleft hright hsr
    ext a b
    exact congrFun hz (a,b)

theorem hierarchyProjector_not_transposeConeSum (n : ℕ) :
    ¬ TransposeConeSum (HasSR (n+1)) (hierarchyProjector n) := by
  let P := hierarchyProjector n
  have hH : P.IsHermitian := hierarchyProjector_hermitian n
  have hI : P * P = P := hierarchyProjector_idempotent n
  have hKIdem : (1-P) * (1-P) = 1-P := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
      hI, sub_self, sub_zero]
  have hK : (1-P).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1-P)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH.eq, hKIdem] at h
    exact h
  apply not_transposeConeSum_of_separator (HasSR (n+1)) P (1-P) hK
  · rw [partialTranspose_sub, partialTranspose_one, hierarchyProjector_partialTranspose]
  · simp only [sub_mul, Matrix.one_mul, hI, sub_self, Matrix.trace_zero]
  · exact hierarchyProjector_nonzero n
  · intro v hv hzero
    have hfixed : P *ᵥ v = v := by
      have hz : v - P *ᵥ v = 0 := by
        simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hzero
      exact (sub_eq_zero.mp hz).symm
    have hm : (fun a b => v (a,b)) ∈ projectionSpace (hierarchyProjector n) := hfixed
    have hz := hierarchyProjector_noSR n (fun a b => v (a,b)) hm hv
    ext p
    exact congrFun (congrFun hz p.1) p.2

/-- For every positive Schmidt-number cutoff there is an actual explicit
nonzero PPT projector outside its transpose-superpositive cone sum. -/
theorem all_levels_explicit_counterexamples (n : ℕ) :
    hierarchyProjector n ≠ 0 ∧ (hierarchyProjector n).PosSemidef ∧
      (partialTranspose (hierarchyProjector n)).PosSemidef ∧
      ¬ TransposeConeSum (HasSR (n+1)) (hierarchyProjector n) := by
  exact ⟨hierarchyProjector_nonzero n, hierarchyProjector_posSemidef n,
    (hierarchyProjector_partialTranspose n).symm ▸ hierarchyProjector_posSemidef n,
    hierarchyProjector_not_transposeConeSum n⟩

/-- No fixed finite cutoff contains all PPT cones, already when the local
dimensions are restricted to the explicit sequence 3^(2^n). -/
theorem no_uniform_finite_cutoff :
    ¬ ∃ k : ℕ, ∀ n : ℕ,
      ∀ R : Matrix (HierarchyIndex n × HierarchyIndex n)
        (HierarchyIndex n × HierarchyIndex n) ℂ,
        R.PosSemidef → (partialTranspose R).PosSemidef →
          TransposeConeSum (HasSR k) R := by
  rintro ⟨k, hk⟩
  have h := hk k (hierarchyProjector k) (hierarchyProjector_posSemidef k)
    ((hierarchyProjector_partialTranspose k).symm ▸ hierarchyProjector_posSemidef k)
  apply hierarchyProjector_not_transposeConeSum k
  exact h.mono (fun v hv => hv.mono (Nat.le_succ k))

#print axioms all_levels_explicit_counterexamples
#print axioms no_uniform_finite_cutoff

end PPTCone
