import MilneJointMinimum

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
noncomputable section
namespace Milne

theorem joint_exists_unit_direction (v : V3) :
    ∃ n : V3, vSq n = 1 ∧ v = Real.sqrt (vSq v) • n := by
  by_cases hv : v = 0
  · refine ⟨geometryEz,geometryEz_unit,?_⟩
    simp [hv,vSq]
  · have hs : 0 < vSq v := vSq_pos_of_ne_zero hv
    have hl : 0 < Real.sqrt (vSq v) := Real.sqrt_pos.mpr hs
    refine ⟨(Real.sqrt (vSq v))⁻¹ • v, ?_, ?_⟩
    · rw [vSq_smul]
      have hsq := Real.sq_sqrt hs.le
      field_simp
    · rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hl),one_smul]

/-- Lower bound directly for the measured correlation of every density matrix
whose Bob marginal is not pure, with the actual steering-centre definition. -/
theorem arbitrary_joint_correlation_lower_bound (M : CMatrix) (hM : Density M)
    (hr : blochLength (partialB M) < 1) :
    (max 0 (steeringCenter M hM*(1+blochLength (partialB M))-1))^2 ≤
      correlationSq M := by
  have hd := bob_det_ne_zero_of_blochLength_lt_one M hM hr
  let N := canonicalize M hM
  have hN : Density N := canonicalize_density M hM hd
  obtain ⟨n,hn,hcn⟩ := joint_exists_unit_direction (geometryLocalA N)
  obtain ⟨m,hm,hbm⟩ := joint_exists_unit_direction (geometryLocalB M)
  have hc : steeringCenter M hM = Real.sqrt (vSq (geometryLocalA N)) := by
    rw [steeringCenter_of_nonsingular M hM hd]
    change center N = _
    rw [center,center_actual_partialA N hN,qubitState_blochSq]
  have hb : blochLength (partialB M) = Real.sqrt (vSq (geometryLocalB M)) := by
    rw [blochLength,center_actual_partialB M hM,qubitState_blochSq]
  rw [← hc] at hcn
  rw [← hb] at hbm
  have hM' : (blochState (geometryLocalA M)
      (blochLength (partialB M) • m) (correlation M)).PosSemidef := by
    rw [← hbm,geometry_density_reconstruction M hM]
    exact hM.1
  have hcentre : geometryLocalA M-tVec (correlation M)
      (blochLength (partialB M) • m) =
      ((1-(blochLength (partialB M))^2)*steeringCenter M hM) • n := by
    rw [← hbm,canonicalize_center_numerator M hM hd]
    change (1-vSq (geometryLocalB M)) • geometryLocalA N = _
    rw [hcn,hbm,vSq_smul,hm,mul_one,smul_smul]
  exact joint_correlation_lower_bound (geometryLocalA M) n m (correlation M)
    (steeringCenter M hM) (blochLength (partialB M)) hM' hn hm hr hcentre

def jointLowerX (c r : ℝ) : ℝ := max 0 (c*(1+r)-1)

def jointLowerT (c r : ℝ) : T3 := Matrix.diagonal ![0,0,jointLowerX c r]

def jointLowerA (c r : ℝ) : ℝ := c*(1-r^2)+r*jointLowerX c r

/-- A diagonal, hence separable, density matrix attaining the lower envelope. -/
def jointLowerState (c r : ℝ) : CMatrix :=
  blochState (jointLowerA c r • geometryEz) (r • geometryEz) (jointLowerT c r)

theorem jointLowerX_bounds {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ jointLowerX c r ∧ jointLowerX c r ≤ r := by
  refine ⟨le_max_left _ _,max_le hr0 ?_⟩
  nlinarith

def jointLowerDiag (c r : ℝ) (i : QQ) : ℝ :=
  if i.1 = 0 then
    (if i.2 = 0 then (1+jointLowerA c r+r+jointLowerX c r)/4
      else (1+jointLowerA c r-r-jointLowerX c r)/4)
  else if i.2 = 0 then (1-jointLowerA c r+r-jointLowerX c r)/4
    else (1-jointLowerA c r-r+jointLowerX c r)/4

theorem jointLowerState_diagonal (c r : ℝ) :
    jointLowerState c r = Matrix.diagonal (fun i : QQ => (jointLowerDiag c r i : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [jointLowerState,jointLowerT,jointLowerDiag,blochState,geometryEz,onAlice,onBob,
      pauli,pauliZ,Matrix.diagonal_apply,Fin.sum_univ_three,Pi.smul_apply,smul_eq_mul,
      Prod.ext_iff]
  all_goals ring

theorem jointLowerState_density {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Density (jointLowerState c r) := by
  have hx := jointLowerX_bounds hc0 hc1 hr0 hr1
  have hrsq : 0 ≤ 1-r^2 := by nlinarith
  have hcprod := mul_nonneg hc0 hrsq
  have hrprod := mul_nonneg hr0 hx.1
  have ha0 : 0 ≤ jointLowerA c r := by dsimp [jointLowerA]; linarith
  have hax : jointLowerX c r ≤ jointLowerA c r := by
    have hxc : jointLowerX c r ≤ c*(1+r) := by
      apply max_le
      · exact mul_nonneg hc0 (by linarith)
      · linarith
    have hprod := mul_nonneg (show 0 ≤ 1-r by linarith) (sub_nonneg.mpr hxc)
    dsimp [jointLowerA]
    nlinarith
  have hap : jointLowerA c r+r ≤ 1+jointLowerX c r := by
    have hlo : c*(1+r)-1 ≤ jointLowerX c r := le_max_right _ _
    have h := mul_nonneg (show 0 ≤ 1-r by linarith) (sub_nonneg.mpr hlo)
    dsimp [jointLowerA]
    nlinarith
  have ham : jointLowerA c r+jointLowerX c r ≤ 1+r := by
    by_cases h : c*(1+r)-1 ≤ 0
    · have hx0 : jointLowerX c r = 0 := max_eq_left h
      rw [jointLowerA,hx0]
      nlinarith [mul_nonneg (show 0 ≤ 1-c by linarith) hrsq]
    · have hxe : jointLowerX c r = c*(1+r)-1 := max_eq_right (by linarith)
      rw [jointLowerA,hxe]
      nlinarith [mul_nonneg (show 0 ≤ 1-c by linarith)
        (show 0 ≤ 1+r by linarith)]
  constructor
  · rw [jointLowerState_diagonal]
    apply Matrix.posSemidef_diagonal_iff.mpr
    rintro ⟨i,j⟩
    apply RCLike.ofReal_nonneg.mpr
    fin_cases i <;> fin_cases j
    · change 0 ≤ (1+jointLowerA c r+r+jointLowerX c r)/4
      linarith [hx.1]
    · change 0 ≤ (1+jointLowerA c r-r-jointLowerX c r)/4
      linarith
    · change 0 ≤ (1-jointLowerA c r+r-jointLowerX c r)/4
      linarith
    · change 0 ≤ (1-jointLowerA c r-r+jointLowerX c r)/4
      linarith
  · exact blochState_trace _ _ _

theorem jointLowerState_bob_length {c r : ℝ} (hr0 : 0 ≤ r) :
    blochLength (partialB (jointLowerState c r)) = r := by
  rw [jointLowerState,blochLength,blochState_blochSqB,vSq_smul,geometryEz_unit,mul_one,
    Real.sqrt_sq hr0]

theorem jointLowerState_correlationSq (c r : ℝ) :
    correlationSq (jointLowerState c r) = (jointLowerX c r)^2 := by
  simp [jointLowerState,blochState_correlationSq,jointLowerT,tSq,
    Matrix.diagonal_apply,Fin.sum_univ_three]

theorem jointLowerState_center {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    steeringCenter (jointLowerState c r)
      (jointLowerState_density hc0 hc1 hr0 hr1.le) = c := by
  let hM := jointLowerState_density hc0 hc1 hr0 hr1.le
  have hlen : blochLength (partialB (jointLowerState c r)) < 1 := by
    rw [jointLowerState_bob_length hr0]
    exact hr1
  have hd := bob_det_ne_zero_of_blochLength_lt_one (jointLowerState c r) hM hlen
  rw [steeringCenter_coordinates (jointLowerState c r) hM hd]
  have hnum : geometryLocalA (jointLowerState c r)-tVec (correlation (jointLowerState c r))
      (geometryLocalB (jointLowerState c r)) = (1-r^2) • (c • geometryEz) := by
    rw [jointLowerState,geometryLocalA_blochState,geometryLocalB_blochState,
      blochState_correlations]
    ext i
    fin_cases i <;> simp [jointLowerA,jointLowerT,tVec,geometryEz,
      Fin.sum_univ_three,Matrix.diagonal_apply] <;> ring
  have hsq : vSq (geometryLocalB (jointLowerState c r)) = r^2 := by
    rw [jointLowerState,geometryLocalB_blochState,vSq_smul,geometryEz_unit,mul_one]
  have hnz : 1-r^2 ≠ 0 := by nlinarith
  rw [hnum,hsq,smul_smul,inv_mul_cancel₀ hnz,one_smul,vSq_smul,
    geometryEz_unit,mul_one,Real.sqrt_sq hc0]

/-- The exact minimum in the set of actual density-matrix correlation values. -/
theorem jointSteeringLower_isLeast {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsLeast (jointSteeringSpectrum c r) ((jointLowerX c r)^2) := by
  constructor
  · refine ⟨jointLowerState c r,jointLowerState_density hc0 hc1 hr0 hr1.le,
      jointLowerState_center hc0 hc1 hr0 hr1,jointLowerState_bob_length hr0,
      jointLowerState_correlationSq c r⟩
  · rintro x ⟨M,hM,hc,hr,hx⟩
    have hlen : blochLength (partialB M) < 1 := by rwa [hr]
    have h := arbitrary_joint_correlation_lower_bound M hM hlen
    simpa [hc,hr,hx,jointLowerX] using h

end Milne
