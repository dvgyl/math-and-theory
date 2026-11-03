import MilneOneSided
import MilneGeometryConsequences

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Negative quadratic Hessian for the complete one-sided filtering orbit. -/
def orbitK (c : V3) (S : T3) : T3 :=
  (tSq S-vSq c) • (1 : T3) - S.transpose*S

theorem orbitK_hermitian (c : V3) (S : T3) : (orbitK c S).IsHermitian := by
  change (orbitK c S)ᴴ = orbitK c S
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbitK,Matrix.conjTranspose_apply,Matrix.mul_apply,Matrix.one_apply,
      Matrix.transpose_apply,Fin.sum_univ_three]
  all_goals ring

/-- The objective is derived from the full filter norm identity. -/
theorem orbit_physical_quadratic_identity (c b : V3) (S : T3) :
    orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b =
      (1-vSq b)*(tSq S-vSq c)+vSq (c+tVec S b) := by
  simp [orbitQuadratic,orbitK,tSq,vSq,vDot,tVec,ttVec,
    Matrix.mul_apply,Matrix.one_apply,Matrix.transpose_apply,Fin.sum_univ_three,
    Pi.add_apply]
  ring

/-- Exact canonical conditional-output formula, before any positivity
assumption.  The canonical Bob marginal makes the trace identically one. -/
theorem canonical_bobWeighted_fano (c b : V3) (S : T3) :
    bobWeighted (blochState c 0 S) (1+spin b) = qubitState (c+tVec S b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [bobWeighted,partialA,blochState,onAlice,onBob,qubitState,spin,
      pauli,pauliZ,tVec,Matrix.mul_apply,Matrix.one_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im,Pi.add_apply]
  all_goals ring

theorem spin_plus_squared (n : V3) (hn : vSq n = 1) :
    (1+spin n)*(1+spin n) = (2:ℂ) • (1+spin n) := by
  have hs : spin n*spin n = (1 : Matrix Q Q ℂ) := by
    rw [spin_squared,hn]
    simp
  calc
    (1+spin n)*(1+spin n) = 1+spin n+spin n+spin n*spin n := by noncomm_ring
    _ = (2:ℂ) • (1+spin n) := by
      rw [hs]
      ext i j
      simp
      ring

/-- Positivity of a physical canonical state implies every endpoint belongs
to the Bloch ball.  The proof uses a projective compression, not invertibility. -/
theorem canonical_endpoint_in_ball (c b : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (hb : vSq b = 1) :
    vSq (c+tVec S b) ≤ 1 := by
  have hF : (1+spin b).IsHermitian := Matrix.isHermitian_one.add (spin_hermitian b)
  have hP := hM.mul_mul_conjTranspose_same (onBob (1+spin b))
  rw [(onBob_hermitian hF).eq] at hP
  have hA := partialA_psd hP
  have hout : partialA (onBob (1+spin b)*blochState c 0 S*onBob (1+spin b)) =
      (2:ℂ) • qubitState (c+tVec S b) := by
    rw [partialA_bob_cycle,spin_plus_squared b hb,onBob_smul,
      Matrix.mul_smul,partialA_smul]
    change (2:ℂ) • bobWeighted (blochState c 0 S) (1+spin b) = _
    rw [canonical_bobWeighted_fano]
  rw [hout] at hA
  have h := blochSq_psd_le hA
  have hs : blochSq ((2:ℂ) • qubitState (c+tVec S b)) = 4*vSq (c+tVec S b) := by
    simp [blochSq,qubitState,spin,vSq,Matrix.one_apply,Fin.sum_univ_three,
      Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  have ht : (Matrix.trace ((2:ℂ) • qubitState (c+tVec S b))).re = 2 := by
    rw [Matrix.trace_smul,qubitState_trace]
    norm_num
  rw [hs,ht] at h
  nlinarith

theorem orbit_physical_boundary (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (b : V3) (hb : vSq b = 1) :
    orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b ≤ 1 := by
  rw [orbit_physical_quadratic_identity,hb]
  simpa using canonical_endpoint_in_ball c b S hM hb

/-- The exact inverse-matrix criterion, with its sphere bound proved from
positivity of an actual 4-by-4 canonical density matrix. -/
theorem physical_orbit_violation_iff (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) :
    (∃ b : V3, vSq b < 1 ∧
      1 < orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b) ↔
      (orbitK c S).PosDef ∧
      vSq (orbitVertex (ttVec S c) (orbitK c S)) < 1 ∧
      1 < tSq S+vDot (ttVec S c) (orbitVertex (ttVec S c) (orbitK c S)) := by
  exact orbit_violation_iff_inverse (tSq S) (ttVec S c) (orbitK c S)
    (orbitK_hermitian c S) (orbit_physical_boundary c S hM)

end Milne
