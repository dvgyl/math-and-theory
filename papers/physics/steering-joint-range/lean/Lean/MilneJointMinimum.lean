import MilneCenterCoordinates
import MilneTraceNorm

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

/-- Unnormalized conditional Alice matrix for a general Bob projective
outcome. It remains meaningful when the outcome probability is zero. -/
theorem joint_bobWeighted_bloch (a b m : V3) (T : T3) :
    bobWeighted (blochState a b T) (1-spin m) =
      (1/2:ℂ) • ((((1-vDot b m):ℝ):ℂ) • (1 : Matrix Q Q ℂ) +
        spin (a-tVec T m)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [bobWeighted,partialA,blochState,onAlice,onBob,spin,pauli,pauliZ,
      vDot,tVec,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,
      Pi.sub_apply,pow_two]
  all_goals ring

theorem joint_bob_compression (a b m : V3) (T : T3) (hm : vSq m = 1) :
    partialA (onBob (1-spin m) * blochState a b T * onBob (1-spin m)) =
      (((1-vDot b m):ℝ):ℂ) • (1 : Matrix Q Q ℂ) + spin (a-tVec T m) := by
  rw [partialA_bob_cycle,spin_complement_squared m hm,onBob_smul,
    Matrix.mul_smul,partialA_smul]
  change (2:ℂ) • bobWeighted (blochState a b T) (1-spin m) = _
  rw [joint_bobWeighted_bloch]
  simp [smul_smul]

theorem joint_projector_trace (d : ℝ) (u n : V3) :
    (Matrix.trace (((d:ℂ) • (1 : Matrix Q Q ℂ)+spin u) * (1-spin n))).re =
      2*(d-vDot u n) := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,spin,vDot,
    Matrix.one_apply,Fin.sum_univ_two,Fin.sum_univ_three,
    Complex.mul_re,Complex.mul_im]
  ring

/-- Nonnegativity of the joint `--` probability in arbitrary unit directions,
derived directly from the positivity of the actual two-qubit matrix. -/
theorem joint_product_probability_nonneg (a b n m : V3) (T : T3)
    (hM : (blochState a b T).PosSemidef) (hn : vSq n = 1) (hm : vSq m = 1) :
    0 ≤ 1-vDot a n-vDot b m+vDot n (tVec T m) := by
  have hB := hM.mul_mul_conjTranspose_same (onBob (1-spin m))
  rw [(onBob_hermitian (Matrix.isHermitian_one.sub (spin_hermitian m))).eq] at hB
  have hA := partialA_psd hB
  rw [joint_bob_compression a b m T hm] at hA
  have hn' : vSq (-n) ≤ 1 := by simpa [vSq,Pi.neg_apply] using hn.le
  have hP := qubitBall_psd (-n) hn'
  have he : 1+spin (-n) = (1-spin n) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spin] <;> ring
  rw [he] at hP
  have h := geometry_trace_product_nonneg hA hP
  rw [joint_projector_trace] at h
  have hid : vDot (a-tVec T m) n = vDot a n-vDot n (tVec T m) := by
    simp [vDot,Pi.sub_apply,Fin.sum_univ_three]
    ring
  rw [hid] at h
  linarith

theorem joint_directional_cauchy (T : T3) (n m : V3)
    (hn : vSq n = 1) (hm : vSq m = 1) :
    (vDot n (tVec T m))^2 ≤ tSq T := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun ij => T ij.1 ij.2) (fun ij => n ij.1*m ij.2)
  have hleft : (∑ ij : Fin 3 × Fin 3, T ij.1 ij.2*(n ij.1*m ij.2)) =
      vDot n (tVec T m) := by
    simp [Fintype.sum_prod_type,vDot,tVec,Finset.mul_sum,mul_assoc,mul_left_comm]
  have hright : (∑ ij : Fin 3 × Fin 3, (n ij.1*m ij.2)^2) = 1 := by
    simp only [Fintype.sum_prod_type,mul_pow,← Finset.mul_sum,← Finset.sum_mul]
    change vSq n*vSq m=1
    rw [hn,hm,mul_one]
  rw [hleft,hright,mul_one] at h
  simpa [tSq,Fintype.sum_prod_type] using h

/-- Sharp lower correlation inequality at prescribed centre direction and Bob
marginal. Only the marginal length is required to be below one. -/
theorem joint_correlation_lower_bound (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    (max 0 (c*(1+r)-1))^2 ≤ tSq T := by
  let q := vDot n (tVec T m)
  have hp := joint_product_probability_nonneg a (r • m) n m T hM hn hm
  have hb : vDot (r • m) m = r := by rw [vDot_smul_self,hm,mul_one]
  have ha : vDot a n = (1-r^2)*c+r*q := by
    have h := congrArg (fun v => vDot v n) hcentre
    dsimp only at h
    have ht : vDot (a-tVec T (r • m)) n = vDot a n-r*q := by
      simp [q,vDot,tVec,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
        Fin.sum_univ_three]
      ring
    rw [ht,vDot_smul_self,hn,mul_one] at h
    linarith
  rw [hb,ha] at hp
  have hfac : 0 ≤ (1-r)*(q-(c*(1+r)-1)) := by nlinarith [hp]
  have hq : c*(1+r)-1 ≤ q := by
    have hd : 0 < 1-r := by linarith
    have := (nonneg_of_mul_nonneg_right hfac hd)
    linarith
  have hcs := joint_directional_cauchy T n m hn hm
  by_cases hlo : c*(1+r)-1 ≤ 0
  · rw [max_eq_left hlo]
    have ht : 0 ≤ tSq T := by
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    simpa using ht
  · have hl : 0 ≤ c*(1+r)-1 := by linarith
    rw [max_eq_right hl]
    change q^2 ≤ tSq T at hcs
    nlinarith

end Milne
