module
public import MilneFiltering

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Milne

/-- The positive square root of twice Bob's marginal. -/
noncomputable def bobFilter (M : CMatrix) (hM : Density M) : Matrix Q Q ℂ :=
  ((partialB_psd hM.1).add (partialB_psd hM.1)).sqrt

/-- Standard canonical representative, when Bob's marginal is invertible. -/
noncomputable def canonicalize (M : CMatrix) (hM : Density M) : CMatrix :=
  onBob (bobFilter M hM)⁻¹ * M * onBob (bobFilter M hM)⁻¹

theorem bobFilter_hermitian (M : CMatrix) (hM : Density M) :
    (bobFilter M hM).IsHermitian :=
  ((partialB_psd hM.1).add (partialB_psd hM.1)).posSemidef_sqrt.1

theorem bobFilter_sq (M : CMatrix) (hM : Density M) :
    bobFilter M hM * bobFilter M hM = (2:ℂ) • partialB M := by
  rw [bobFilter, Matrix.PosSemidef.sqrt_mul_self]
  ext i j
  simp
  ring

theorem bobFilter_trace (M : CMatrix) (hM : Density M) :
    Matrix.trace (bobFilter M hM * bobFilter M hM) = 2 := by
  rw [bobFilter_sq, Matrix.trace_smul, trace_partialB, hM.2]
  simp

theorem bobFilter_isUnit (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) : IsUnit (bobFilter M hM).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hd := congrArg Matrix.det (bobFilter_sq M hM)
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_smul] at hd
  norm_num [Q] at hd
  exact hdet hd

theorem canonicalize_psd (M : CMatrix) (hM : Density M) :
    (canonicalize M hM).PosSemidef := by
  have h := hM.1.mul_mul_conjTranspose_same (onBob (bobFilter M hM)⁻¹)
  have hi := onBob_hermitian (bobFilter_hermitian M hM).inv
  simpa only [hi.eq, canonicalize] using h

theorem canonicalize_partialB (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    partialB (canonicalize M hM) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  let F := bobFilter M hM
  have hF := bobFilter_isUnit M hM hdet
  have hB : partialB M = (1/2:ℂ) • (F*F) := by
    rw [bobFilter_sq]
    simp [smul_smul]
  rw [canonicalize, partialB_filter, hB, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  change F⁻¹ * (F*F) * F⁻¹ = 1
  rw [Matrix.nonsing_inv_mul_cancel_left F F hF, Matrix.mul_nonsing_inv F hF]

theorem canonicalize_density (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) : Density (canonicalize M hM) := by
  refine ⟨canonicalize_psd M hM, ?_⟩
  rw [← trace_partialB, canonicalize_partialB M hM hdet, Matrix.trace_smul]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem canonicalize_reconstruction (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    onBob (bobFilter M hM) * canonicalize M hM * onBob (bobFilter M hM) = M := by
  let F := bobFilter M hM
  have hF := bobFilter_isUnit M hM hdet
  have hleft : onBob F * onBob F⁻¹ = (1:CMatrix) := by
    rw [← onBob_mul, Matrix.mul_nonsing_inv F hF, onBob_one]
  have hright : onBob F⁻¹ * onBob F = (1:CMatrix) := by
    rw [← onBob_mul, Matrix.nonsing_inv_mul F hF, onBob_one]
  change onBob F * (onBob F⁻¹ * M * onBob F⁻¹) * onBob F = M
  calc
    _ = (onBob F * onBob F⁻¹) * M * (onBob F⁻¹ * onBob F) := by
      noncomm_ring
    _ = M := by rw [hleft, hright]; simp

/-- The fully entangled-fraction bound for an arbitrary complex
two-qubit density matrix with invertible Bob marginal. The steering center
is computed from its canonical representative, not supplied as a hypothesis. -/
theorem arbitrary_entangled_overlap_bound (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    overlap M v ≤ 1 - center (canonicalize M hM) / 2 := by
  have h := filtered_entangled_overlap_bound (canonicalize M hM)
    (canonicalize_density M hM hdet) (canonicalize_partialB M hM hdet)
    (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM) v hv
  rwa [canonicalize_reconstruction M hM hdet] at h

end Milne
