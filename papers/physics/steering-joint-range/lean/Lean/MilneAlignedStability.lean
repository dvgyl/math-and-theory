import MilneAlignedState
import MilneTraceNorm

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

noncomputable section
namespace Milne

/-- The canonical maximizing state in the radial basis with positive
00--11 coherence. It is a Bob Pauli-X conjugate of `obese c`. -/
def alignedObese (c : ℝ) : CMatrix :=
  alignedState c (1-c) 0 ((Real.sqrt (1-c)/2:ℝ):ℂ) 0

theorem alignedObese_hermitian (c : ℝ) : (alignedObese c).IsHermitian :=
  alignedState_hermitian c (1-c) 0 _ 0

theorem alignedObese_eq_bobX {c : ℝ} (hc1 : c ≤ 1) :
    alignedObese c = onBob (pauli 0)*obese c*onBob (pauli 0) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hsC : (Real.sqrt (1-c):ℂ)^2 = (1-c:ℂ) := by exact_mod_cast hs
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [alignedObese,alignedState,alignedA,alignedD,alignedC,
      obese,obeseVector,pure,onBob,pauli,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def,
      Complex.mul_re,Complex.mul_im,Prod.ext_iff,← pow_two,hs,hsC]
  all_goals ring

theorem alignedObese_density {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Density (alignedObese c) := by
  apply alignedState_density
  change (alignedObese c).PosSemidef
  rw [alignedObese_eq_bobX hc1]
  have h := (obese_psd hc0).mul_mul_conjTranspose_same (onBob (pauli 0))
  simpa only [(onBob_hermitian (pauli_hermitian 0)).eq] using h

theorem alignedObese_correlationSq {c : ℝ} (hc1 : c ≤ 1) :
    correlationSq (alignedObese c) = (1-c)*(3-c) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  rw [alignedObese,alignedState_correlationSq]
  simp [Complex.normSq_apply]
  nlinarith

theorem aligned_difference_hermitian (c t w : ℝ) (z v : ℂ) :
    (alignedState c t z (w:ℂ) v-alignedObese c).IsHermitian :=
  (alignedState_hermitian c t z (w:ℂ) v).sub (alignedObese_hermitian c)

/-- Exact matrix Hilbert--Schmidt distance, including every coherence.
This is not a scalar hypothesis supplied to a stability theorem. -/
theorem aligned_hs_distance_identity (c t w : ℝ) (z v : ℂ) :
    matrixHsSq (alignedState c t z (w:ℂ) v-alignedObese c) =
      (1-c-t)^2/4 + 4*Complex.normSq z + 2*Complex.normSq v +
        2*(w-Real.sqrt (1-c)/2)^2 := by
  simp [matrixHsSq,alignedObese,alignedState,alignedA,alignedD,alignedC,
    Fintype.sum_prod_type,Fin.sum_univ_two,Complex.normSq_apply,
    Complex.star_def,Complex.mul_re,Complex.mul_im,map_ofNat]
  ring

theorem aligned_deficit_identity {c : ℝ} (hc1 : c ≤ 1)
    (t w : ℝ) (z v : ℂ) :
    rigidityDeficit c (alignedState c t z (w:ℂ) v) =
      (1-c)^2-t^2 + 8*((Real.sqrt (1-c)/2)^2-w^2) -
        16*Complex.normSq z-8*Complex.normSq v := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  rw [rigidityDeficit,alignedState_correlationSq]
  simp [Complex.normSq_apply]
  nlinarith

/-- Actual PSD minors and the positive-coherence gauge give the complete
matrix estimate that was previously left as a supplied scalar hypothesis. -/
theorem aligned_hs_preliminary {c t w : ℝ} {z v : ℂ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (hw0 : 0 ≤ w)
    (hM : (alignedState c t z (w:ℂ) v).PosSemidef) :
    4*matrixHsSq (alignedState c t z (w:ℂ) v-alignedObese c) ≤
      rigidityDeficit c (alignedState c t z (w:ℂ) v) +
        (1-c-t)*(3+3*c-t) := by
  have ht1 := alignedState_radial_range c t z (w:ℂ) v hM
  have hmz := alignedState_minor_z c t z (w:ℂ) v hM
  have hmv := alignedState_minor_v c t z (w:ℂ) v hM
  have hmw := alignedState_minor_w c t z (w:ℂ) v hM
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hs0 := Real.sqrt_nonneg (1-c)
  have hy : 0 ≤ (1-c-t)*(3-c+t) := mul_nonneg (by linarith) (by linarith)
  have hwsq : w^2 ≤ (Real.sqrt (1-c)/2)^2 := by
    simp only [Complex.normSq_ofReal] at hmw
    nlinarith
  have hwle : w ≤ Real.sqrt (1-c)/2 := by nlinarith
  have hprod := mul_nonneg hw0 (show 0 ≤ Real.sqrt (1-c)/2-w by linarith)
  have hcoh : (w-Real.sqrt (1-c)/2)^2 ≤ (Real.sqrt (1-c)/2)^2-w^2 := by
    nlinarith
  rw [aligned_hs_distance_identity,aligned_deficit_identity (le_of_lt hc1)]
  nlinarith

/-- Quantitative Hilbert--Schmidt rigidity for an actual canonical density
matrix in the radial basis and positive-coherence gauge. -/
theorem aligned_hs_stability {c t w : ℝ} {z v : ℂ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (hw0 : 0 ≤ w)
    (hM : (alignedState c t z (w:ℂ) v).PosSemidef) :
    4*matrixHsSq (alignedState c t z (w:ℂ) v-alignedObese c) ≤
      rigidityDeficit c (alignedState c t z (w:ℂ) v) *
        (1/2+(2+c)/(1-c+t)) ∧
    rigidityDeficit c (alignedState c t z (w:ℂ) v) *
        (1/2+(2+c)/(1-c+t)) ≤
      rigidityDeficit c (alignedState c t z (w:ℂ) v)*(5+c)/(2*(1-c)) := by
  have ht1 := alignedState_radial_range c t z (w:ℂ) v hM
  have hgap := alignedState_deficit_radial c t z (w:ℂ) v hM
  have hprod : 0 ≤ 2*(1-c-t)*(1-c+t) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hδ : 0 ≤ rigidityDeficit c (alignedState c t z (w:ℂ) v) := le_trans hprod hgap
  exact radial_stability_constant hc0 hc1 ht0 ht1 hδ hgap
    (aligned_hs_preliminary hc0 hc1 ht0 hw0 hM)

/-- Genuine trace-norm rigidity, obtained from the proven matrix distance
and the spectral trace norm. Every rank-deficient canonical state is allowed. -/
theorem aligned_trace_stability {c t w : ℝ} {z v : ℂ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (hw0 : 0 ≤ w)
    (hM : (alignedState c t z (w:ℂ) v).PosSemidef) :
    (hermitianTraceNorm (aligned_difference_hermitian c t w z v))^2 ≤
      rigidityDeficit c (alignedState c t z (w:ℂ) v)*(5+c)/(2*(1-c)) := by
  have hHS := aligned_hs_stability hc0 hc1 ht0 hw0 hM
  exact (hermitianTraceNorm_sq_le_four_hs
    (aligned_difference_hermitian c t w z v)).trans (hHS.1.trans hHS.2)

end Milne

#print axioms Milne.aligned_hs_preliminary
#print axioms Milne.aligned_hs_stability
#print axioms Milne.aligned_trace_stability
