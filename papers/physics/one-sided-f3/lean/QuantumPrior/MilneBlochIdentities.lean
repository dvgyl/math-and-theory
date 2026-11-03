/- Reused from the existing Milne formalization in the user workspace.
   Provenance and original SHA256 are recorded in QuantumPrior/PROVENANCE.json.
   Only local import module prefixes were adapted; proof statements and bodies are unchanged. -/
import QuantumPrior.MilneCorrelation

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Partial traces of the exact Fano matrix recover its given marginal vectors. -/
theorem blochState_partialA (a b : V3) (T : T3) :
    partialA (blochState a b T) = qubitState a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialA, blochState, qubitState, spin, pauli, pauliZ, onAlice, onBob,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.one_apply]
  all_goals ring

theorem blochState_partialB (a b : V3) (T : T3) :
    partialB (blochState a b T) = qubitState b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialB, blochState, qubitState, spin, pauli, pauliZ, onAlice, onBob,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.one_apply]
  all_goals ring

theorem qubitState_trace (a : V3) : Matrix.trace (qubitState a) = 1 := by
  simp [qubitState, spin, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

theorem blochState_trace (a b : V3) (T : T3) : Matrix.trace (blochState a b T) = 1 := by
  rw [← trace_partialA, blochState_partialA, qubitState_trace]

theorem blochState_density (a b : V3) (T : T3)
    (hM : (blochState a b T).PosSemidef) : Density (blochState a b T) :=
  ⟨hM, blochState_trace a b T⟩

theorem qubitState_blochSq (a : V3) : blochSq (qubitState a) = vSq a := by
  simp [qubitState, spin, blochSq, vSq, Matrix.one_apply, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem blochState_blochSqA (a b : V3) (T : T3) :
    blochSq (partialA (blochState a b T)) = vSq a := by
  rw [blochState_partialA, qubitState_blochSq]

theorem blochState_blochSqB (a b : V3) (T : T3) :
    blochSq (partialB (blochState a b T)) = vSq b := by
  rw [blochState_partialB, qubitState_blochSq]

theorem blochState_center_formula (a b : V3) (T : T3) :
    center (blochState a b T) = Real.sqrt (vSq a) := by
  rw [center,blochState_blochSqA]

theorem vSq_smul (c : ℝ) (n : V3) : vSq (c • n) = c^2 * vSq n := by
  simp [vSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem blochState_radial_center (c : ℝ) (n : V3) (T : T3)
    (hc : 0 ≤ c) (hn : vSq n = 1) :
    center (blochState (c • n) 0 T) = c := by
  rw [blochState_center_formula,vSq_smul,hn,mul_one,Real.sqrt_sq hc]

theorem qubitState_zero : qubitState (0 : V3) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitState,spin]

theorem blochState_canonical (a : V3) (T : T3) :
    partialB (blochState a 0 T) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  rw [blochState_partialB,qubitState_zero]

end Milne
