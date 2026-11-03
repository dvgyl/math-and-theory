/- Reused from the existing Milne formalization in the user workspace.
   Provenance and original SHA256 are recorded in QuantumPrior/PROVENANCE.json.
   Only local import module prefixes were adapted; proof statements and bodies are unchanged. -/
import QuantumPrior.MilneGeometry
import QuantumPrior.MilneBlochIdentities

/-!
# Bridge from arbitrary density matrices to the geometric inequality

This module reconstructs every Hermitian trace-one complex 4 by 4 matrix
from its actual Pauli expectations. Thus the Bloch-form geometric theorem
applies to every density matrix, without any parametrization hypothesis.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def geometryLocalA (M : CMatrix) : V3 := fun i =>
  (Matrix.trace (M * onAlice (pauli i))).re

def geometryLocalB (M : CMatrix) : V3 := fun i =>
  (Matrix.trace (M * onBob (pauli i))).re

theorem geometry_onAlice_hermitian (i : Fin 3) :
    (onAlice (pauli i)).IsHermitian := by
  change (onAlice (pauli i))ᴴ = onAlice (pauli i)
  ext p q
  by_cases h : p.2 = q.2
  · simp only [Matrix.conjTranspose_apply, onAlice, if_pos h,
      if_pos h.symm]
    exact (pauli_hermitian i).apply p.1 q.1
  · have hr : q.2 ≠ p.2 := Ne.symm h
    simp [Matrix.conjTranspose_apply, onAlice, h, hr]

theorem geometry_onBob_hermitian (i : Fin 3) :
    (onBob (pauli i)).IsHermitian := by
  change (onBob (pauli i))ᴴ = onBob (pauli i)
  ext p q
  by_cases h : p.1 = q.1
  · simp only [Matrix.conjTranspose_apply, onBob, if_pos h,
      if_pos h.symm]
    exact (pauli_hermitian i).apply p.2 q.2
  · have hr : q.1 ≠ p.1 := Ne.symm h
    simp [Matrix.conjTranspose_apply, onBob, h, hr]

/-- Pauli completeness, before assuming Hermiticity or normalization. -/
theorem geometry_pauli_reconstruction_polynomial (M : CMatrix) :
    M = fun p q => (1/4:ℂ) *
      (Matrix.trace M * (if p = q then 1 else 0) +
        (∑ i : Fin 3, Matrix.trace (M * onAlice (pauli i)) *
          onAlice (pauli i) p q) +
        (∑ i : Fin 3, Matrix.trace (M * onBob (pauli i)) *
          onBob (pauli i) p q) +
        ∑ i : Fin 3, ∑ j : Fin 3, Matrix.trace (M * pauliPair i j) *
          pauli i p.1 q.1 * pauli j p.2 q.2) := by
  ext ⟨p1,p2⟩ ⟨q1,q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    apply Complex.ext <;>
    simp [pauliPair, pauli, pauliZ, onAlice, onBob,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, Prod.ext_iff]
  all_goals ring

/-- A physically complete reconstruction from local and joint observables. -/
theorem geometry_density_reconstruction (M : CMatrix) (hM : Density M) :
    blochState (geometryLocalA M) (geometryLocalB M) (correlation M) = M := by
  have ha (i : Fin 3) : (geometryLocalA M i : ℂ) =
      Matrix.trace (M * onAlice (pauli i)) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (trace_mul_hermitian_im hM.1.1 (geometry_onAlice_hermitian i)).symm
  have hb (i : Fin 3) : (geometryLocalB M i : ℂ) =
      Matrix.trace (M * onBob (pauli i)) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (trace_mul_hermitian_im hM.1.1 (geometry_onBob_hermitian i)).symm
  have ht (i j : Fin 3) : (correlation M i j : ℂ) =
      Matrix.trace (M * pauliPair i j) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (trace_mul_hermitian_im hM.1.1 (pauliPair_hermitian i j)).symm
  have hp := geometry_pauli_reconstruction_polynomial M
  ext p q
  have he := congrFun (congrFun hp p) q
  simp only [hM.2, one_mul] at he
  simpa only [blochState, ha, hb, ht] using he.symm

/-- Every two-qubit density matrix satisfies the full geometric LMI in
its directly measured Bloch and correlation coefficients. No rank assumptions. -/
theorem all_density_geometry_matrix_psd (M : CMatrix) (hM : Density M) :
    (geometryMatrix (geometryLocalA M) (geometryLocalB M) (correlation M)).PosSemidef := by
  apply geometry_matrix_psd
  rw [geometry_density_reconstruction M hM]
  exact hM.1

theorem all_density_geometry_directional (M : CMatrix) (hM : Density M) (n : V3) :
    0 ≤ vSq n * (1 + vSq (geometryLocalA M) - vSq (geometryLocalB M) -
      correlationSq M) - 2*(vDot (geometryLocalA M) n)^2 +
      2*vSq (ttVec (correlation M) n) := by
  have hp : (blochState (geometryLocalA M) (geometryLocalB M) (correlation M)).PosSemidef := by
    rw [geometry_density_reconstruction M hM]
    exact hM.1
  exact geometry_directional (geometryLocalA M) (geometryLocalB M) n (correlation M) hp

#print axioms geometry_density_reconstruction
#print axioms all_density_geometry_matrix_psd
#print axioms all_density_geometry_directional

end Milne
