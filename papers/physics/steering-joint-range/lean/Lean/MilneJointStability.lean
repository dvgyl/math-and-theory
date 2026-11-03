import MilneJointMinimumPhysical
import MilneTraceDistance

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

def jointOuter (n m : V3) : T3 := fun i j => n i*m j

theorem joint_tSq_nonneg (T : T3) : 0 ≤ tSq T :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem joint_tSq_eq_zero_iff (T : T3) : tSq T = 0 ↔ T=0 := by
  constructor
  · intro h
    ext i j
    have hrow : (∑ k, T i k^2) ≤ tSq T :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hij : T i j^2 ≤ ∑ k, T i k^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hz : T i j^2=0 := by rw [h] at hrow; nlinarith [sq_nonneg (T i j)]
    exact sq_eq_zero_iff.mp hz
  · intro h
    simp [h,tSq]

theorem joint_matrix_vector_bound (T : T3) (m : V3) (hm : vSq m = 1) :
    vSq (tVec T m) ≤ tSq T := by
  apply Finset.sum_le_sum
  intro i hi
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun j => T i j) m
  change (tVec T m i)^2 ≤ (∑ j, T i j^2)*vSq m at h
  simpa only [hm,mul_one] using h

theorem joint_outer_gap_identity (T : T3) (n m : V3) (x : ℝ)
    (hn : vSq n = 1) (hm : vSq m = 1) :
    tSq (T-x • jointOuter n m) =
      tSq T-2*x*vDot n (tVec T m)+x^2 := by
  have he : tSq (T-x • jointOuter n m) =
      tSq T-2*x*vDot n (tVec T m)+x^2*vSq n*vSq m := by
    simp [tSq,vDot,tVec,vSq,jointOuter,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,Fin.sum_univ_three]
    ring
  rw [he,hn,hm,mul_one,mul_one]

theorem joint_directional_lower (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    c*(1+r)-1 ≤ vDot n (tVec T m) := by
  have hp := joint_product_probability_nonneg a (r • m) n m T hM hn hm
  have hb : vDot (r • m) m = r := by rw [vDot_smul_self,hm,mul_one]
  have ha : vDot a n = (1-r^2)*c+r*vDot n (tVec T m) := by
    have h := congrArg (fun v => vDot v n) hcentre
    dsimp only at h
    have ht : vDot (a-tVec T (r • m)) n = vDot a n-r*vDot n (tVec T m) := by
      simp [vDot,tVec,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
      ring
    rw [ht,vDot_smul_self,hn,mul_one] at h
    linarith
  rw [hb,ha] at hp
  have hfac : 0 ≤ (1-r)*(vDot n (tVec T m)-(c*(1+r)-1)) := by nlinarith
  have h := nonneg_of_mul_nonneg_right hfac (show 0 < 1-r by linarith)
  linarith

/-- The correlation deficit controls the full matrix displacement from the
unique lower-envelope correlation matrix, including the zero-correlation region. -/
theorem joint_lower_matrix_rigidity (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    tSq (T-jointLowerX c r • jointOuter n m) ≤ tSq T-(jointLowerX c r)^2 := by
  rw [joint_outer_gap_identity T n m _ hn hm]
  have hq := joint_directional_lower a n m T c r hM hn hm hr hcentre
  by_cases hlo : c*(1+r)-1 ≤ 0
  · have hx : jointLowerX c r=0 := max_eq_left hlo
    simp [hx]
  · have hx : jointLowerX c r=c*(1+r)-1 := max_eq_right (by linarith)
    rw [hx]
    have hp := mul_nonneg (show 0 ≤ c*(1+r)-1 by linarith) (sub_nonneg.mpr hq)
    nlinarith

theorem joint_lower_vector_identity (a n m : V3) (T : T3) (c r : ℝ)
    (hm : vSq m = 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    a-jointLowerA c r • n = r • tVec (T-jointLowerX c r • jointOuter n m) m := by
  have hout : tVec (jointOuter n m) m = n := by
    ext i
    calc
      tVec (jointOuter n m) m i = n i*vSq m := by
        simp [tVec,jointOuter,vSq,Finset.mul_sum,pow_two,mul_assoc]
      _ = n i := by rw [hm,mul_one]
  have hlinear : tVec (T-jointLowerX c r • jointOuter n m) m =
      tVec T m-jointLowerX c r • n := by
    calc
      tVec (T-jointLowerX c r • jointOuter n m) m =
          tVec T m-jointLowerX c r • tVec (jointOuter n m) m := by
        ext i
        simp [tVec,Matrix.sub_apply,Matrix.smul_apply,Pi.sub_apply,Pi.smul_apply,
          smul_eq_mul,Finset.sum_sub_distrib,Finset.mul_sum,sub_mul,mul_assoc]
      _ = tVec T m-jointLowerX c r • n := by rw [hout]
  rw [hlinear]
  ext i
  have h := congrFun hcentre i
  simp [tVec,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three] at h ⊢
  dsimp [jointLowerA]
  nlinarith

theorem joint_lower_vector_rigidity (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    vSq (a-jointLowerA c r • n) ≤ r^2*(tSq T-(jointLowerX c r)^2) := by
  rw [joint_lower_vector_identity a n m T c r hm hcentre,vSq_smul]
  have h := (joint_matrix_vector_bound (T-jointLowerX c r • jointOuter n m) m hm).trans
    (joint_lower_matrix_rigidity a n m T c r hM hn hm hr hcentre)
  exact mul_le_mul_of_nonneg_left h (sq_nonneg r)

theorem joint_bloch_hermitian (a b : V3) (T : T3) : (blochState a b T).IsHermitian := by
  change (blochState a b T)ᴴ = blochState a b T
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [blochState,onAlice,onBob,pauli,pauliZ,Matrix.conjTranspose_apply,
      Complex.star_def,Complex.mul_re,Complex.mul_im,Fin.sum_univ_three,Prod.ext_iff]
  all_goals ring

theorem joint_bloch_hs_difference (a b a' b' : V3) (T T' : T3) :
    4*matrixHsSq (blochState a b T-blochState a' b' T') =
      vSq (a-a')+vSq (b-b')+tSq (T-T') := by
  simp [matrixHsSq,blochState,onAlice,onBob,pauli,pauliZ,vSq,tSq,
    Matrix.sub_apply,Pi.sub_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
    Fin.sum_univ_three,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Prod.ext_iff]
  ring

/-- A genuine spectral trace-norm bound, in the same physical Bloch axes.
The reference matrix is the explicit diagonal minimizer rotated into n,m. -/
theorem joint_lower_trace_rigidity (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    (hermitianTraceNorm (hM.1.sub (joint_bloch_hermitian
      (jointLowerA c r • n) (r • m) (jointLowerX c r • jointOuter n m))))^2 ≤
      (1+r^2)*(tSq T-(jointLowerX c r)^2) := by
  have hmtrx := joint_lower_matrix_rigidity a n m T c r hM hn hm hr hcentre
  have hvec := joint_lower_vector_rigidity a n m T c r hM hn hm hr hcentre
  have htrace := hermitianTraceNorm_sq_le_four_hs (hM.1.sub (joint_bloch_hermitian
      (jointLowerA c r • n) (r • m) (jointLowerX c r • jointOuter n m)))
  rw [joint_bloch_hs_difference] at htrace
  have hzero : vSq (r • m-r • m)=0 := by simp [vSq]
  rw [hzero] at htrace
  nlinarith

/-- Exact lower-endpoint rigidity in actual correlation coordinates. -/
theorem joint_lower_equality_iff (a n m : V3) (T : T3) (c r : ℝ)
    (hM : (blochState a (r • m) T).PosSemidef)
    (hn : vSq n = 1) (hm : vSq m = 1) (hr : r < 1)
    (hcentre : a-tVec T (r • m) = ((1-r^2)*c) • n) :
    tSq T=(jointLowerX c r)^2 ↔
      T=jointLowerX c r • jointOuter n m ∧ a=jointLowerA c r • n := by
  constructor
  · intro he
    have h := joint_lower_matrix_rigidity a n m T c r hM hn hm hr hcentre
    rw [he,sub_self] at h
    have hz := le_antisymm h (joint_tSq_nonneg _)
    have hT : T=jointLowerX c r • jointOuter n m :=
      sub_eq_zero.mp ((joint_tSq_eq_zero_iff _).mp hz)
    have ha := joint_lower_vector_identity a n m T c r hm hcentre
    rw [hT,sub_self] at ha
    refine ⟨hT,sub_eq_zero.mp ?_⟩
    calc
      a-jointLowerA c r • n = r • tVec (0:T3) m := ha
      _ = 0 := by ext i; simp [tVec]
  · rintro ⟨hT,ha⟩
    rw [hT]
    have hid : tSq (jointLowerX c r • jointOuter n m) =
        (jointLowerX c r)^2*vSq n*vSq m := by
      simp [tSq,jointOuter,Matrix.smul_apply,smul_eq_mul,vSq,Fin.sum_univ_three]
      ring
    rw [hid,hn,hm,mul_one,mul_one]

end Milne
