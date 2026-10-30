import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace NesterovThresholdModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure ConvexBody (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

noncomputable def ConvexBody.proj (K : ConvexBody E) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)

theorem ConvexBody.proj_mem (K : ConvexBody E) (x : E) : K.proj x ∈ K.carrier :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)).1

theorem ConvexBody.proj_variational (K : ConvexBody E) (x y : E) (hy : y∈K.carrier) :
    inner (x-K.proj x) (y-K.proj x) ≤ (0:ℝ) := by
  exact (norm_eq_iInf_iff_real_inner_le_zero K.convex (K.proj_mem x)).mp
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)).2 y hy

theorem ConvexBody.proj_dist_le (K : ConvexBody E) (x y : E) :
    ‖K.proj x-K.proj y‖≤‖x-y‖ := by
  have h1 := K.proj_variational x (K.proj y) (K.proj_mem y)
  have h2 := K.proj_variational y (K.proj x) (K.proj_mem x)
  have hid : inner (x-y) (K.proj x-K.proj y)-‖K.proj x-K.proj y‖^2 =
      -(inner (x-K.proj x) (K.proj y-K.proj x)+inner (y-K.proj y) (K.proj x-K.proj y)) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (K.proj y) (K.proj x)]
    ring
  have hc := real_inner_le_norm (x-y) (K.proj x-K.proj y)
  by_cases hz : ‖K.proj x-K.proj y‖=0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0<‖K.proj x-K.proj y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_right hp).mp
    nlinarith

theorem ConvexBody.proj_eq_self (K : ConvexBody E) {x : E} (hx : x∈K.carrier) :
    K.proj x=x := by
  have hv := K.proj_variational x x hx
  rw [real_inner_self_eq_norm_sq] at hv
  have hz : ‖x-K.proj x‖=0 := by nlinarith [norm_nonneg (x-K.proj x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

noncomputable def ConvexBody.gradient (K : ConvexBody E) (ε : ℝ) (x : E) : E :=
  K.proj (ε⁻¹ • x)
noncomputable def ConvexBody.potential (K : ConvexBody E) (ε : ℝ) (x : E) : ℝ :=
  inner (K.gradient ε x) x-ε*‖K.gradient ε x‖^2/2

theorem ConvexBody.gradient_mem (K : ConvexBody E) (ε : ℝ) (x : E) :
    K.gradient ε x∈K.carrier := K.proj_mem _

theorem ConvexBody.gradient_variational (K : ConvexBody E) {ε : ℝ} (he : 0<ε)
    (x y : E) (hy : y∈K.carrier) :
    inner (x-ε • K.gradient ε x) (y-K.gradient ε x) ≤ (0:ℝ) := by
  have hh := mul_nonpos_of_nonneg_of_nonpos he.le
    (K.proj_variational (ε⁻¹ • x) y hy)
  rw [←real_inner_smul_left,smul_sub,smul_smul,mul_inv_cancel₀ (ne_of_gt he),one_smul] at hh
  exact hh

theorem ConvexBody.dual_bound (K : ConvexBody E) {ε : ℝ} (he : 0<ε)
    (x y : E) (hy : y∈K.carrier) :
    inner y x-ε*‖y‖^2/2≤K.potential ε x := by
  have hv := K.gradient_variational he x y hy
  have hs := sq_nonneg ‖y-K.gradient ε x‖
  rw [norm_sub_sq_real] at hs
  have hm := mul_nonneg he.le hs
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hv
  have hxy := real_inner_comm x y
  have hxg := real_inner_comm x (K.gradient ε x)
  have hgy := real_inner_comm (K.gradient ε x) y
  unfold ConvexBody.potential
  nlinarith

theorem ConvexBody.support (K : ConvexBody E) {ε : ℝ} (he : 0<ε) (x y : E) :
    K.potential ε x+inner (K.gradient ε x) (y-x)≤K.potential ε y := by
  have hh := K.dual_bound he y (K.gradient ε x) (K.gradient_mem ε x)
  simp only [ConvexBody.potential,inner_sub_right] at *
  linarith

omit [CompleteSpace E] in
theorem convexOn_univ_of_support {f : E→ℝ} (g : E→E)
    (hs : ∀x y,f x+inner (g x) (y-x)≤f y) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x+b • y
  have hx := mul_le_mul_of_nonneg_left (hs z x) ha
  have hy := mul_le_mul_of_nonneg_left (hs z y) hb
  have he : a • (x-z)+b • (y-z)=0 := by
    calc
      _=(a • x+b • y)-(a+b) • z := by rw [add_smul,smul_sub,smul_sub];abel
      _=0 := by rw [hab,one_smul];exact sub_self _
  have hi : a*inner (g z) (x-z)+b*inner (g z) (y-z)=0 := by
    rw [←inner_smul_right,←inner_smul_right,←inner_add_right,he,inner_zero_right]
  have hf : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  change f z≤a*f x+b*f y
  nlinarith

theorem ConvexBody.potential_convex (K : ConvexBody E) {ε : ℝ} (he : 0<ε) :
    ConvexOn ℝ Set.univ (K.potential ε) := convexOn_univ_of_support _ (K.support he)

theorem ConvexBody.gradient_dist_le (K : ConvexBody E) {ε : ℝ} (he : 0<ε) (x y : E) :
    ‖K.gradient ε x-K.gradient ε y‖≤ε⁻¹*‖x-y‖ := by
  have hh := K.proj_dist_le (ε⁻¹ • x) (ε⁻¹ • y)
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr he)] at hh
  exact hh

theorem ConvexBody.potential_remainder (K : ConvexBody E) {ε : ℝ} (he : 0<ε) (x h : E) :
    ‖K.potential ε (x+h)-K.potential ε x-inner (K.gradient ε x) h‖≤ε⁻¹*‖h‖^2 := by
  have hl := K.support he x (x+h)
  have hu := K.support he (x+h) x
  have hd : x-(x+h) = -h := by abel
  simp only [add_sub_cancel_left] at hl
  rw [hd,inner_neg_right] at hu
  have hp := K.gradient_dist_le he (x+h) x
  simp only [add_sub_cancel_left] at hp
  have hc := real_inner_le_norm (K.gradient ε (x+h)-K.gradient ε x) h
  have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg h)
  rw [inner_sub_left] at hc
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  nlinarith

theorem ConvexBody.potential_hasFDerivAt (K : ConvexBody E) {ε : ℝ} (he : 0<ε) (x : E) :
    HasFDerivAt (K.potential ε) (innerSL ℝ (K.gradient ε x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hb : (fun h:E=>K.potential ε (x+h)-K.potential ε x-(innerSL ℝ (K.gradient ε x)) h)
      =O[𝓝 0] (fun h:E=>‖h‖^2) := by
    apply Asymptotics.IsBigO.of_bound ε⁻¹
    filter_upwards [] with h
    change ‖K.potential ε (x+h)-K.potential ε x-inner (K.gradient ε x) h‖≤ε⁻¹*‖‖h‖^2‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using K.potential_remainder he x h
  exact hb.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by decide : 1<2))

theorem ConvexBody.potential_hasGradientAt (K : ConvexBody E) {ε : ℝ} (he : 0<ε) (x:E) :
    HasGradientAt (K.potential ε) (K.gradient ε x) x := by
  exact K.potential_hasFDerivAt he x

end NesterovThresholdModel
