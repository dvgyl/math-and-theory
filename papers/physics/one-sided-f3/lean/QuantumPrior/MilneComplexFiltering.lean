/- Reused from the existing Milne formalization in the user workspace.
   Provenance and original SHA256 are recorded in QuantumPrior/PROVENANCE.json.
   Only local import module prefixes were adapted; proof statements and bodies are unchanged. -/
import QuantumPrior.MilneSteering
import QuantumPrior.MilneBlochIdentities

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- A completely general complex Bob-local filter, using its adjoint. -/
def complexFiltered (M : CMatrix) (F : Matrix Q Q ℂ) : CMatrix :=
  onBob F * M * onBob Fᴴ

/-- The polarized determinant identity with distinct left and right factors. -/
theorem qubit_trace_covariance_general (A B F G : Matrix Q Q ℂ) :
    Matrix.trace ((F*A*G)*(F*B*G)) -
      Matrix.trace (F*A*G)*Matrix.trace (F*B*G) =
    (F.det*G.det)*(Matrix.trace (A*B)-Matrix.trace A*Matrix.trace B) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_two]
  ring

theorem bobBlock_filter_general (M : CMatrix) (F G : Matrix Q Q ℂ) (a c : Q) :
    bobBlock (onBob F*M*onBob G) a c = F*bobBlock M a c*G := by
  ext b d
  fin_cases a <;> fin_cases c <;>
    simp [bobBlock,onBob,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]

/-- Full determinant covariance for arbitrary complex filters, including
singular ones. This is an exact matrix polynomial identity. -/
theorem purityDifference_filter_general (M : CMatrix) (F G : Matrix Q Q ℂ) :
    purityDifference (onBob F*M*onBob G) = (F.det*G.det)*purityDifference M := by
  rw [purityDifference_blocks,purityDifference_blocks]
  simp_rw [bobBlock_filter_general,qubit_trace_covariance_general]
  simp only [Finset.mul_sum]

theorem complexFiltered_psd {M : CMatrix} (hM : M.PosSemidef) (F : Matrix Q Q ℂ) :
    (complexFiltered M F).PosSemidef := by
  have h := hM.mul_mul_conjTranspose_same (onBob F)
  rwa [← onBob_conjTranspose] at h

theorem complexFiltered_bob_marginal (M : CMatrix)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (F : Matrix Q Q ℂ) :
    partialB (complexFiltered M F) = (1/2:ℂ) • (F*Fᴴ) := by
  rw [complexFiltered,partialB_filter,hB]
  simp [Matrix.mul_smul,Matrix.smul_mul]

theorem complexFiltered_density (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (F : Matrix Q Q ℂ)
    (hTr : Matrix.trace (Fᴴ*F) = 2) : Density (complexFiltered M F) := by
  refine ⟨complexFiltered_psd hM.1 F,?_⟩
  rw [← trace_partialB,complexFiltered_bob_marginal M hB F,Matrix.trace_smul,
    Matrix.trace_mul_comm F Fᴴ,hTr]
  norm_num

theorem complexFiltered_purity_covariance (M : CMatrix) (F : Matrix Q Q ℂ) :
    (purityDifference (complexFiltered M F)).re =
      (F*Fᴴ).det.re*(purityDifference M).re := by
  have h := purityDifference_filter_general M F Fᴴ
  rw [← Matrix.det_mul] at h
  have hi : (F*Fᴴ).det.im = 0 :=
    hermitian_det_im (Matrix.posSemidef_self_mul_conjTranspose F).1
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re,hi,zero_mul,sub_zero] using hr

theorem complexFiltered_det_bloch (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (F : Matrix Q Q ℂ)
    (hTr : Matrix.trace (Fᴴ*F) = 2) :
    (F*Fᴴ).det.re = 1-blochSq (partialB (complexFiltered M F)) := by
  have hρ := complexFiltered_density M hM hB F hTr
  have hd := blochSq_det_identity (partialB_psd hρ.1).1
  rw [trace_partialB,hρ.2] at hd
  have hdet : (partialB (complexFiltered M F)).det = (1/4:ℂ)*(F*Fᴴ).det := by
    rw [complexFiltered_bob_marginal M hB F,Matrix.det_smul]
    norm_num [Q]
  rw [hdet] at hd
  norm_num [Complex.mul_re,Complex.mul_im] at hd
  simp only [Matrix.det_mul,Matrix.det_conjTranspose,Complex.star_def,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  nlinarith

/-- Exact Frobenius-norm identity for every complex filter with canonical
normalization. No polar decomposition or full-rank state assumption is used. -/
theorem complexFiltered_correlation_identity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (F : Matrix Q Q ℂ)
    (hTr : Matrix.trace (Fᴴ*F) = 2) :
    correlationSq (complexFiltered M F) =
      (1-blochSq (partialB (complexFiltered M F)))*(correlationSq M-center M^2) +
      blochSq (partialA (complexFiltered M F)) := by
  have hρ := complexFiltered_density M hM hB F hTr
  have hCov := complexFiltered_purity_covariance M F
  rw [complexFiltered_det_bloch M hM hB F hTr] at hCov
  have hCM := correlationSq_purityDifference M hM
  have hzero : blochSq (partialB M) = 0 := by
    rw [hB]
    norm_num [blochSq,Matrix.one_apply,Complex.normSq_apply]
  rw [hzero] at hCM
  have hCρ := correlationSq_purityDifference (complexFiltered M F) hρ
  have hcSq : center M^2 = blochSq (partialA M) :=
    Real.sq_sqrt (blochSq_nonneg _)
  rw [hCρ,hCM,← hcSq,hCov]
  ring

end Milne
