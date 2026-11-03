import MilneGeometry
import MilneBlochIdentities
import MilneRefinement

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem spin_hermitian (n : V3) : (spin n).IsHermitian := by
  change (spin n)ᴴ = spin n
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, Matrix.conjTranspose_apply, Complex.star_def]
  all_goals ring

theorem onAlice_hermitian {F : Matrix Q Q ℂ} (hF : F.IsHermitian) :
    (onAlice F).IsHermitian := by
  change (onAlice F)ᴴ = onAlice F
  ext i j
  simp only [Matrix.conjTranspose_apply, onAlice]
  by_cases h : i.2 = j.2
  · rw [if_pos h.symm,if_pos h]
    exact hF.apply i.1 j.1
  · rw [if_neg (Ne.symm h),if_neg h,star_zero]

theorem onAlice_smul (t : ℂ) (F : Matrix Q Q ℂ) :
    onAlice (t • F) = t • onAlice F := by
  ext i j
  by_cases h : i.2 = j.2 <;> simp [onAlice,h]

theorem partialB_alice_cycle (M : CMatrix) (F G : Matrix Q Q ℂ) :
    partialB (onAlice F * M * onAlice G) = partialB (M * onAlice (G*F)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialB,onAlice,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
  all_goals ring

theorem spin_squared (n : V3) : spin n * spin n = (vSq n : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin,vSq,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem spin_complement_squared (n : V3) (hn : vSq n = 1) :
    (1-spin n)*(1-spin n) = (2:ℂ) • (1-spin n) := by
  have hs : spin n * spin n = (1 : Matrix Q Q ℂ) := by
    rw [spin_squared,hn]
    simp
  calc
    (1-spin n)*(1-spin n) = 1-spin n-spin n+spin n*spin n := by noncomm_ring
    _ = (2:ℂ) • (1-spin n) := by
      rw [hs]
      ext i j
      simp
      ring

theorem blochState_aliceWeighted (a n : V3) (T : T3) :
    partialB (blochState a 0 T * onAlice (1-spin n)) =
      (1/2:ℂ) • ((((1-vDot a n):ℝ):ℂ) • (1 : Matrix Q Q ℂ) - spin (ttVec T n)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [partialB,blochState,onAlice,onBob,spin,pauli,pauliZ,vDot,ttVec,
      Matrix.mul_apply,Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
      Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem vDot_smul_self (c : ℝ) (n : V3) : vDot (c • n) n = c*vSq n := by
  simp [vDot,vSq,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,pow_two,mul_assoc]

/-- A positive projective compression of a canonical state. The formula
also applies to a zero-probability outcome at c=1. -/
theorem canonical_radial_compression (c : ℝ) (n : V3) (T : T3)
    (hn : vSq n = 1) :
    partialB (onAlice (1-spin n) * blochState (c • n) 0 T * onAlice (1-spin n)) =
      (((1-c):ℝ):ℂ) • (1 : Matrix Q Q ℂ) - spin (ttVec T n) := by
  rw [partialB_alice_cycle,spin_complement_squared n hn,onAlice_smul,
    Matrix.mul_smul,partialB_smul,blochState_aliceWeighted,vDot_smul_self,hn,mul_one]
  simp [smul_smul]

theorem scalar_sub_spin_blochSq (t : ℝ) (s : V3) :
    blochSq ((t:ℂ) • (1 : Matrix Q Q ℂ) - spin s) = 4*vSq s := by
  simp [blochSq,spin,vSq,Matrix.one_apply,Fin.sum_univ_three,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im]
  ring

theorem scalar_sub_spin_trace (t : ℝ) (s : V3) :
    (Matrix.trace ((t:ℂ) • (1 : Matrix Q Q ℂ) - spin s)).re = 2*t := by
  simp [spin,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

/-- Sharp radial feasibility, obtained without dividing by 1-c or by any
state eigenvalue. It therefore includes c=1 and every rank-deficient case. -/
theorem canonical_radial_feasibility (c : ℝ) (n : V3) (T : T3)
    (hn : vSq n = 1) (hM : (blochState (c • n) 0 T).PosSemidef) :
    vSq (ttVec T n) ≤ (1-c)^2 := by
  have hP : (onAlice (1-spin n)).IsHermitian :=
    onAlice_hermitian (Matrix.isHermitian_one.sub (spin_hermitian n))
  have hρ := hM.mul_mul_conjTranspose_same (onAlice (1-spin n))
  rw [hP.eq] at hρ
  have hB := partialB_psd hρ
  rw [canonical_radial_compression c n T hn] at hB
  have h := blochSq_psd_le hB
  rw [scalar_sub_spin_blochSq,scalar_sub_spin_trace] at h
  nlinarith

/-- The canonical purity deficit controls the radial geometric deficit. -/
theorem canonical_radial_deficit_bound (c : ℝ) (n : V3) (T : T3)
    (hc : 0 ≤ c) (hn : vSq n = 1)
    (hM : (blochState (c • n) 0 T).PosSemidef) :
    2*((1-c)^2-vSq (ttVec T n)) ≤ canonicalCorrelationDeficit (blochState (c • n) 0 T) := by
  have h := geometry_radial c n T hn hM
  rw [canonicalCorrelationDeficit,blochState_radial_center c n T hc hn,
    blochState_correlationSq]
  nlinarith

/-- Quantitative global rigidity in the radial shape and marginal length,
derived from the full physical filter identity and the spin-flip inequality. -/
theorem filtered_envelope_radial_gap (c : ℝ) (n : V3) (T : T3)
    (hc0 : 0 ≤ c) (hc : c ≤ 2/3) (hn : vSq n = 1)
    (hM : (blochState (c • n) 0 T).PosSemidef)
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let M := blochState (c • n) 0 T
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    steeringDenominator c*(r-optimalFilterLength c)^2 +
      2*(1-r^2)*((1-c)^2-vSq (ttVec T n)) ≤ steeringEnvelopeSq c-correlationSq ρ := by
  let M := blochState (c • n) 0 T
  let ρ := onBob F * M * onBob F
  let r := blochLength (partialB ρ)
  have hD : Density M := blochState_density _ _ _ hM
  have hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := blochState_canonical _ _
  have hcenter : center M = c := blochState_radial_center c n T hc0 hn
  have hcM : center M ≤ 2/3 := by rwa [hcenter]
  have hρ : Density ρ := filtered_density M hD hB F hF hTr
  have hr0 : 0 ≤ r := blochLength_nonneg _
  have hr1 : r ≤ 1 := by
    have h := blochLength_psd_le (partialB_psd hρ.1)
    rw [trace_partialB,hρ.2] at h
    exact h
  have hrSq : 0 ≤ 1-r^2 := by nlinarith
  have hdelta := canonical_radial_deficit_bound c n T hc0 hn hM
  have hprod := mul_le_mul_of_nonneg_left hdelta hrSq
  have hA := marginalDeficit_nonneg M hD hB F hF hTr
  have hid := filtered_envelope_deficit_identity M hD hB F hF hTr hcM
  dsimp only at hid ⊢
  rw [hcenter] at hid
  change steeringEnvelopeSq c-correlationSq ρ =
    steeringDenominator c*(r-optimalFilterLength c)^2 +
    (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F at hid
  change steeringDenominator c*(r-optimalFilterLength c)^2 +
    2*(1-r^2)*((1-c)^2-vSq (ttVec T n)) ≤ steeringEnvelopeSq c-correlationSq ρ
  change (1-r^2)*(2*((1-c)^2-vSq (ttVec T n))) ≤
    (1-r^2)*canonicalCorrelationDeficit M at hprod
  nlinarith

end Milne
