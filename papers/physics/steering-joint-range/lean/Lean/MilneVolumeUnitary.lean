import MilneLocalUnitary
import MilneVolumeSharpness

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 16000

noncomputable section
namespace Milne

/-- Cubic Pauli invariant that detects signed correlation determinant.
This polynomial identity does not require positivity or invertibility. -/
theorem canonical_bloch_trace_cube (a : V3) (T : T3) :
    16*(Matrix.trace (blochState a 0 T * blochState a 0 T * blochState a 0 T)).re =
      1+3*vSq a+3*tSq T-6*T.det := by
  simp [blochState,onAlice,onBob,pauli,pauliZ,vSq,tSq,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,
    Fin.sum_univ_two,Fin.sum_univ_three,Matrix.det_fin_three,
    Complex.mul_re,Complex.mul_im,Prod.ext_iff]
  ring

theorem geometryLocalB_zero_of_canonical (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) : geometryLocalB M = 0 := by
  have hr := geometry_density_reconstruction M hM
  have hb := congrArg partialB hr
  rw [blochState_partialB,hB] at hb
  have h0 := congrArg (fun A : Matrix Q Q ℂ => (A 0 1).re) hb
  have h1 := congrArg (fun A : Matrix Q Q ℂ => (A 0 1).im) hb
  have h2 := congrArg (fun A : Matrix Q Q ℂ => (A 0 0).re) hb
  simp [qubitState,spin,Matrix.one_apply,Complex.mul_re,Complex.mul_im] at h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The signed determinant is determined by physical cubic trace, local
Bloch length and the actual correlation norm on canonical inputs. -/
theorem canonical_density_trace_cube (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    16*(Matrix.trace (M*M*M)).re =
      1+3*center M^2+3*correlationSq M-6*Matrix.det (correlation M) := by
  have hr := geometry_density_reconstruction M hM
  rw [geometryLocalB_zero_of_canonical M hM hB] at hr
  have h := canonical_bloch_trace_cube (geometryLocalA M) (correlation M)
  rw [hr] at h
  have ha := congrArg partialA hr
  rw [blochState_partialA] at ha
  have hs : vSq (geometryLocalA M) = center M^2 := by
    rw [center,Real.sq_sqrt (blochSq_nonneg _),← ha,qubitState_blochSq]
  rw [hs] at h
  exact h

theorem rigidityConj_matrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    rigidityConj U A * rigidityConj U B = rigidityConj U (A*B) := by
  unfold rigidityConj
  calc
    ((U:Matrix ι ι ℂ)*A*(U:Matrix ι ι ℂ)ᴴ)*
        ((U:Matrix ι ι ℂ)*B*(U:Matrix ι ι ℂ)ᴴ) =
      (U:Matrix ι ι ℂ)*A*((U:Matrix ι ι ℂ)ᴴ*(U:Matrix ι ι ℂ))*B*
        (U:Matrix ι ι ℂ)ᴴ := by noncomm_ring
    _ = (U:Matrix ι ι ℂ)*(A*B)*(U:Matrix ι ι ℂ)ᴴ := by
      rw [rigidity_unitary_adjoint_mul]
      simp only [mul_one]
      noncomm_ring

theorem rigidityConj_trace_cube {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Matrix.trace (rigidityConj U A*rigidityConj U A*rigidityConj U A) =
      Matrix.trace (A*A*A) := by
  rw [rigidityConj_matrix_mul,rigidityConj_matrix_mul,rigidityConj_trace]

/-- Signed determinant invariance under actual local unitaries, derived
from trace invariants without supplying an SO(3) parametrization. -/
theorem localConjugate_correlation_det (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    Matrix.det (correlation (localConjugate U V M)) = Matrix.det (correlation M) := by
  have h := canonical_density_trace_cube M hM hB
  have hN := canonical_density_trace_cube (localConjugate U V M)
    (localConjugate_density U V M hM) (localConjugate_canonical U V M hB)
  rw [localConjugate_center U V M hM,localConjugate_correlationSq U V M hM] at hN
  have htr : Matrix.trace (localConjugate U V M*localConjugate U V M*
      localConjugate U V M) = Matrix.trace (M*M*M) := by
    exact rigidityConj_trace_cube (aliceUnitary U*bobUnitary V) M
  rw [htr] at hN
  linarith

end Milne

#print axioms Milne.canonical_bloch_trace_cube
#print axioms Milne.localConjugate_correlation_det
