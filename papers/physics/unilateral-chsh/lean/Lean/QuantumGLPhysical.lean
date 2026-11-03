import QuantumLocalUnitary
import QuantumSupport

/-! Invertible filtering of every actual density matrix has strictly positive
success normalization and produces another density matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

theorem filtered_inverse (ρ : State) (F : QubitMatrix) (hF : F.det≠0) :
    filtered (filtered ρ F) F⁻¹=ρ := by
  rw [filtered_compose,Matrix.nonsing_inv_mul F (isUnit_iff_ne_zero.mpr hF),filtered_one]

theorem filtered_trace_positive (ρ : State) (F : QubitMatrix)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) (hF : F.det≠0) :
    0<(Matrix.trace (filtered ρ F)).re := by
  have hX := filtered_psd hρ F
  have hn := psd_trace_nonneg hX
  apply lt_of_le_of_ne hn
  intro hz
  have hzero := psd_eq_zero_of_trace_re_zero hX hz.symm
  have hρ0 : ρ=0 := by
    have hi := filtered_inverse ρ F hF
    rw [hzero] at hi
    simpa [filtered] using hi.symm
  rw [hρ0] at ht
  simp at ht

theorem state_posSemidef_smul_real (X : State) (hX : X.PosSemidef)
    (r : ℝ) (hr : 0≤r) : ((r : ℂ) • X).PosSemidef := by
  constructor
  · change ((r : ℂ) • X)ᴴ=(r : ℂ) • X
    rw [Matrix.conjTranspose_smul,hX.1.eq]
    simp
  · intro x
    rw [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul]
    exact mul_nonneg (by exact_mod_cast hr) (hX.2 x)

theorem normalizedFiltered_density (ρ : State) (F : QubitMatrix)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) (hF : F.det≠0) :
    (normalizedFiltered ρ F).PosSemidef ∧ Matrix.trace (normalizedFiltered ρ F)=1 := by
  let X := filtered ρ F
  let p := (Matrix.trace X).re
  have hX : X.PosSemidef := filtered_psd hρ F
  have hp : 0<p := filtered_trace_positive ρ F hρ ht hF
  have hpn : (p : ℂ)≠0 := by exact_mod_cast (ne_of_gt hp)
  have him : (Matrix.trace X).im=0 := by
    simpa using hermitian_product_trace_real X 1 hX.1 Matrix.isHermitian_one
  have htr : Matrix.trace X=(p : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  constructor
  · change (normalizeState X).PosSemidef
    simpa only [normalizeState,Complex.ofReal_inv] using
      state_posSemidef_smul_real X hX p⁻¹ (le_of_lt (inv_pos.mpr hp))
  · change Matrix.trace ((p⁻¹ : ℂ) • X)=1
    rw [Matrix.trace_smul,htr]
    change (p : ℂ)⁻¹*(p : ℂ)=1
    exact inv_mul_cancel₀ hpn

end UnilateralCHSH.Quantum
