import MilneJointStability

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

def jointTensor (A B : Matrix Q Q ℂ) : CMatrix :=
  fun i j => A i.1 j.1 * B i.2 j.2

theorem jointTensor_mul (A B C D : Matrix Q Q ℂ) :
    jointTensor A B * jointTensor C D = jointTensor (A*C) (B*D) := by
  ext i j
  simp [jointTensor, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem jointTensor_conjTranspose (A B : Matrix Q Q ℂ) :
    (jointTensor A B)ᴴ = jointTensor Aᴴ Bᴴ := by
  ext i j
  simp [jointTensor, Matrix.conjTranspose_apply]

theorem jointTensor_psd {A B : Matrix Q Q ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (jointTensor A B).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (jointTensor hA.sqrt hB.sqrt)
  rw [jointTensor_conjTranspose, hA.posSemidef_sqrt.1.eq, hB.posSemidef_sqrt.1.eq,
    jointTensor_mul, hA.sqrt_mul_self, hB.sqrt_mul_self] at h
  exact h

def jointLowerRotated (c r : ℝ) (n m : V3) : CMatrix :=
  blochState (jointLowerA c r • n) (r • m) (jointLowerX c r • jointOuter n m)

theorem jointLowerRotated_decomposition (c r : ℝ) (n m : V3) :
    jointLowerRotated c r n m =
      (((jointLowerDiag c r (0,0)/4 : ℝ):ℂ) • jointTensor (1+spin n) (1+spin m) +
       ((jointLowerDiag c r (0,1)/4 : ℝ):ℂ) • jointTensor (1+spin n) (1+spin (-m))) +
      (((jointLowerDiag c r (1,0)/4 : ℝ):ℂ) • jointTensor (1+spin (-n)) (1+spin m) +
       ((jointLowerDiag c r (1,1)/4 : ℝ):ℂ) • jointTensor (1+spin (-n)) (1+spin (-m))) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [jointLowerRotated,jointLowerDiag,blochState,jointOuter,jointTensor,
      onAlice,onBob,spin,pauli,pauliZ,Fin.sum_univ_three,Pi.smul_apply,smul_eq_mul,
      Matrix.add_apply,Matrix.smul_apply,Pi.neg_apply,Complex.mul_re,Complex.mul_im,
      Prod.ext_iff]
  all_goals ring

/-- The reference in the lower trace-distance estimate is itself a genuine
state in every pair of unit Bloch axes, including all zero-rank boundaries. -/
theorem jointLowerRotated_density {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n m : V3)
    (hn : vSq n = 1) (hm : vSq m = 1) : Density (jointLowerRotated c r n m) := by
  have hn' : vSq (-n) ≤ 1 := by simpa [vSq,Pi.neg_apply] using hn.le
  have hm' : vSq (-m) ≤ 1 := by simpa [vSq,Pi.neg_apply] using hm.le
  have hnp := qubitBall_psd n hn.le
  have hnm := qubitBall_psd (-n) hn'
  have hmp := qubitBall_psd m hm.le
  have hmm := qubitBall_psd (-m) hm'
  have hp (i : QQ) : 0 ≤ jointLowerDiag c r i := by
    have h := psd_diag_nonneg (jointLowerState_density hc0 hc1 hr0 hr1).1 i
    simpa only [jointLowerState_diagonal,Matrix.diagonal_apply_eq,Complex.ofReal_re] using h
  constructor
  · rw [jointLowerRotated_decomposition]
    exact ((psd_real_smul (jointTensor_psd hnp hmp) _ (div_nonneg (hp (0,0)) (by norm_num))).add
      (psd_real_smul (jointTensor_psd hnp hmm) _ (div_nonneg (hp (0,1)) (by norm_num)))).add
      ((psd_real_smul (jointTensor_psd hnm hmp) _ (div_nonneg (hp (1,0)) (by norm_num))).add
      (psd_real_smul (jointTensor_psd hnm hmm) _ (div_nonneg (hp (1,1)) (by norm_num))))
  · exact blochState_trace _ _ _

/-- Physical trace-norm stability with an explicitly certified density matrix
as the reference state. The trace norm is the sum of absolute eigenvalues. -/
theorem joint_physical_trace_rigidity (a n m : V3) (T : T3) (c r : ℝ)
    (hM : Density (blochState a (r • m) T))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hn : vSq n = 1) (hm : vSq m = 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    Density (jointLowerRotated c r n m) ∧
      (hermitianTraceNorm (hM.1.1.sub (joint_bloch_hermitian
        (jointLowerA c r • n) (r • m) (jointLowerX c r • jointOuter n m))))^2 ≤
        (1+r^2)*(tSq T-(jointLowerX c r)^2) := by
  exact ⟨jointLowerRotated_density hc0 hc1 hr0 hr1.le n m hn hm,
    joint_lower_trace_rigidity a n m T c r hM.1 hn hm hr1 hcentre⟩

end Milne
