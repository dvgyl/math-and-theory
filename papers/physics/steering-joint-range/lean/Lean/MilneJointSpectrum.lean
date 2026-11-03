import MilneJointMinimumPhysical
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Continuity

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
noncomputable section
namespace Milne

def jointUpperV (c r : ℝ) : QQ → ℂ := fun i =>
  if i=(0,0) then (Real.sqrt (1+r):ℂ)
  else if i=(1,1) then (Real.sqrt (1-c)*Real.sqrt (1-r):ℝ) else 0

def jointUpperState (c r : ℝ) : CMatrix :=
  (1/2:ℂ) • pure (jointUpperV c r) +
    ((c*(1-r)/2:ℝ):ℂ) • pure (Pi.single (0,1) 1)

def jointUpperT (c r : ℝ) : T3 :=
  let s := Real.sqrt (1-c)*Real.sqrt (1-r)*Real.sqrt (1+r)
  Matrix.diagonal ![s,-s,1-c+c*r]

theorem jointUpperState_psd {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 1) :
    (jointUpperState c r).PosSemidef := by
  simpa [jointUpperState] using
    (psd_real_smul (pure_psd (jointUpperV c r)) (1/2) (by norm_num)).add
      (psd_real_smul (pure_psd (Pi.single (0,1) 1)) (c*(1-r)/2)
        (div_nonneg (mul_nonneg hc (sub_nonneg.mpr hr)) (by norm_num)))

theorem jointUpperState_bloch {c r : ℝ} (hc1 : c ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    jointUpperState c r =
      blochState ((c+(1-c)*r) • geometryEz) (r • geometryEz) (jointUpperT c r) := by
  have hd := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hm := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have hp := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hdm : (Real.sqrt (1-c)*Real.sqrt (1-r))^2 = (1-c)*(1-r) := by
    rw [mul_pow,hd,hm]
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> apply Complex.ext <;>
    simp [jointUpperState,jointUpperV,jointUpperT,pure,blochState,geometryEz,
      onAlice,onBob,pauli,pauliZ,Matrix.diagonal_apply,Fin.sum_univ_three,
      Pi.smul_apply,smul_eq_mul,Complex.normSq_apply,Complex.mul_re,
      Complex.mul_im,Complex.star_def,Prod.ext_iff]
  all_goals nlinarith [hd,hm,hp,hdm]

theorem jointUpperT_sq {c r : ℝ} (hc1 : c ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    tSq (jointUpperT c r) = steeringQuadratic c r := by
  have hd := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hm := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have hp := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  simp [jointUpperT,tSq,Matrix.diagonal_apply,Fin.sum_univ_three,
    mul_pow,hd,hm,hp,steeringQuadratic]
  ring

theorem joint_bloch_convex (a0 a1 b : V3) (T0 T1 : T3) (α : ℝ) :
    ((1-α:ℝ):ℂ) • blochState a0 b T0 + (α:ℂ) • blochState a1 b T1 =
      blochState ((1-α) • a0+α • a1) b ((1-α) • T0+α • T1) := by
  ext i j
  simp [blochState,Pi.add_apply,Matrix.add_apply,Matrix.smul_apply,Pi.smul_apply,
    smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum,Complex.ofReal_add,
    Complex.ofReal_mul,Complex.ofReal_sub,Fin.sum_univ_three]
  ring

def jointPathA (c r α : ℝ) : V3 :=
  (1-α) • (jointLowerA c r • geometryEz)+α • ((c+(1-c)*r) • geometryEz)
def jointPathT (c r α : ℝ) : T3 := (1-α) • jointLowerT c r+α • jointUpperT c r
def jointPathState (c r α : ℝ) : CMatrix :=
  blochState (jointPathA c r α) (r • geometryEz) (jointPathT c r α)

theorem jointPathState_density {c r α : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Density (jointPathState c r α) := by
  constructor
  · have hlo := (jointLowerState_density hc0 hc1 hr0 hr1).1
    have hhi := jointUpperState_psd hc0 hr1
    have h := (psd_real_smul hlo (1-α) (by linarith)).add (psd_real_smul hhi α hα0)
    rw [jointUpperState_bloch hc1 hr0 hr1,jointLowerState,joint_bloch_convex] at h
    exact h
  · exact blochState_trace _ _ _

theorem jointPathState_bob_length {c r α : ℝ} (hr0 : 0 ≤ r) :
    blochLength (partialB (jointPathState c r α)) = r := by
  rw [jointPathState,blochLength,blochState_blochSqB,vSq_smul,geometryEz_unit,mul_one,
    Real.sqrt_sq hr0]

theorem jointPathState_center {c r α : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    steeringCenter (jointPathState c r α)
      (jointPathState_density hc0 hc1 hr0 hr1.le hα0 hα1) = c := by
  let hM := jointPathState_density hc0 hc1 hr0 hr1.le hα0 hα1
  have hlen : blochLength (partialB (jointPathState c r α)) < 1 := by
    rw [jointPathState_bob_length hr0]
    exact hr1
  have hd := bob_det_ne_zero_of_blochLength_lt_one (jointPathState c r α) hM hlen
  rw [steeringCenter_coordinates (jointPathState c r α) hM hd]
  have hnum : geometryLocalA (jointPathState c r α)-tVec (correlation (jointPathState c r α))
      (geometryLocalB (jointPathState c r α)) = (1-r^2) • (c • geometryEz) := by
    rw [jointPathState,geometryLocalA_blochState,geometryLocalB_blochState,
      blochState_correlations]
    ext i
    fin_cases i <;> simp [jointPathA,jointPathT,jointLowerT,jointUpperT,jointLowerA,
      tVec,geometryEz,Matrix.diagonal_apply,Fin.sum_univ_three] <;> ring
  have hsq : vSq (geometryLocalB (jointPathState c r α)) = r^2 := by
    rw [jointPathState,geometryLocalB_blochState,vSq_smul,geometryEz_unit,mul_one]
  have hnz : 1-r^2 ≠ 0 := by nlinarith
  rw [hnum,hsq,smul_smul,inv_mul_cancel₀ hnz,one_smul,vSq_smul,geometryEz_unit,
    mul_one,Real.sqrt_sq hc0]

theorem jointPathState_correlationSq (c r α : ℝ) :
    correlationSq (jointPathState c r α) =
      2*α^2*(Real.sqrt (1-c)*Real.sqrt (1-r)*Real.sqrt (1+r))^2+
        ((1-α)*jointLowerX c r+α*(1-c+c*r))^2 := by
  simp [jointPathState,blochState_correlationSq,jointPathT,jointLowerT,jointUpperT,
    tSq,Matrix.diagonal_apply,Fin.sum_univ_three]
  ring

/-- Every intermediate correlation value is attained by an explicit convex
path of genuine states preserving both the centre and the Bob marginal. -/
theorem jointSteeringSpectrum_eq_Icc {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    jointSteeringSpectrum c r = Set.Icc ((jointLowerX c r)^2) (steeringQuadratic c r) := by
  ext y
  constructor
  · intro hy
    exact ⟨(jointSteeringLower_isLeast hc0 hc1 hr0 hr1).2 hy,
      (jointSteeringQuadratic_isGreatest hc0 hc1 hr0 hr1).2 hy⟩
  · intro hy
    let f : ℝ → ℝ := fun α =>
      2*α^2*(Real.sqrt (1-c)*Real.sqrt (1-r)*Real.sqrt (1+r))^2+
        ((1-α)*jointLowerX c r+α*(1-c+c*r))^2
    have hf : Continuous f := by dsimp [f]; continuity
    have hf0 : f 0 = (jointLowerX c r)^2 := by simp [f]
    have hf1 : f 1 = steeringQuadratic c r := by
      calc
        f 1 = tSq (jointUpperT c r) := by
          simp [f,jointUpperT,tSq,Matrix.diagonal_apply,Fin.sum_univ_three]
          ring
        _ = steeringQuadratic c r := jointUpperT_sq hc1 hr0 hr1.le
    have hy' : y ∈ Set.Icc (f 0) (f 1) := by rwa [hf0,hf1]
    obtain ⟨α,hα,hval⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
      hf.continuousOn hy'
    refine ⟨jointPathState c r α,jointPathState_density hc0 hc1 hr0 hr1.le hα.1 hα.2,
      jointPathState_center hc0 hc1 hr0 hr1 hα.1 hα.2,
      jointPathState_bob_length hr0,?_⟩
    rw [jointPathState_correlationSq]
    exact hval

end Milne
