import RadialHuber

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace NesterovModel

section GeneralMinimizers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem radialHuber_eq_norm_iff (x : E) : radialHuber x=‖x‖ ↔ 1≤‖x‖ := by
  constructor
  · intro hh
    by_contra hn
    have hx : ‖x‖<1 := lt_of_not_ge hn
    rw [radialHuber_of_norm_le hx.le] at hh
    have hp := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hx)
    nlinarith
  · exact radialHuber_of_one_le_norm

theorem valley_eq_zero_iff {e : E} (he : ‖e‖=1) (x : E) :
    valley e x=0 ↔ ∃ t : ℝ, 1≤t ∧ x=t • e := by
  constructor
  · intro hz
    have hn := norm_le_radialHuber x
    have hi := real_inner_le_norm e x
    rw [he,one_mul] at hi
    have hv : radialHuber x=inner e x := sub_eq_zero.mp hz
    have hH : radialHuber x=‖x‖ := le_antisymm (hv.trans_le hi) hn
    have hix : inner e x=‖x‖ := hv.symm.trans hH
    have hsq : ‖x-‖x‖ • e‖^2=0 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x), he, mul_one, real_inner_smul_right,
        real_inner_comm e x, hix]
      ring
    have hzero : x-‖x‖ • e=0 := norm_eq_zero.mp (pow_eq_zero hsq)
    exact ⟨‖x‖,(radialHuber_eq_norm_iff x).mp hH,sub_eq_zero.mp hzero⟩
  · rintro ⟨t,ht,rfl⟩
    have hnorm : ‖t • e‖=t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), he, mul_one]
    unfold valley
    rw [radialHuber_of_one_le_norm (by rw [hnorm]; exact ht), hnorm,
      real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring

theorem valley_axis_zero {e : E} (he : ‖e‖=1) : valley e e=0 :=
  (valley_eq_zero_iff he e).mpr ⟨1,le_refl _,by rw [one_smul]⟩

theorem valley_isMin_iff {e : E} (he : ‖e‖=1) (x : E) :
    (∀ y, valley e x≤valley e y) ↔ ∃ t : ℝ, 1≤t ∧ x=t • e := by
  rw [←valley_eq_zero_iff he x]
  constructor
  · intro hh
    have hl := hh e
    rw [valley_axis_zero he] at hl
    exact le_antisymm hl (valley_nonneg he x)
  · intro hx y
    rw [hx]
    exact valley_nonneg he y

end GeneralMinimizers

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def axis : Plane := EuclideanSpace.single 0 1
noncomputable def point (x y : ℝ) : Plane :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y
noncomputable def potential (z : Plane) : ℝ := valley axis z
noncomputable def gradient (z : Plane) : Plane := valleyGradient axis z

@[simp] theorem axis_norm : ‖axis‖=1 := by simp [axis]
@[simp] theorem axis_first : axis 0=1 := by simp [axis]
@[simp] theorem axis_second : axis 1=0 := by simp [axis]
@[simp] theorem point_first (x y : ℝ) : point x y 0=x := by simp [point]
@[simp] theorem point_second (x y : ℝ) : point x y 1=y := by simp [point]

theorem inner_axis (z : Plane) : inner axis z=z 0 := by
  simp only [axis, EuclideanSpace.inner_single_left, starRingEnd_apply,
    star_one, one_mul]

theorem potential_formula (z : Plane) :
    potential z=(if ‖z‖≤1 then (‖z‖^2+1)/2 else ‖z‖)-z 0 := by
  rw [potential,valley,inner_axis]
  rfl

theorem norm_eq_sqrt (z : Plane) : ‖z‖=Real.sqrt ((z 0)^2+(z 1)^2) := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem norm_sq_eq (z : Plane) : ‖z‖^2=(z 0)^2+(z 1)^2 := by
  rw [norm_eq_sqrt, Real.sq_sqrt (by positivity)]

theorem first_coordinate_le_norm (z : Plane) : z 0≤‖z‖ := by
  have hh := real_inner_le_norm axis z
  simpa only [inner_axis,axis_norm,one_mul] using hh

theorem gradient_first (z : Plane) : gradient z 0=z 0/(max 1 ‖z‖)-1 := by
  simp only [gradient,valleyGradient,radialProj,PiLp.sub_apply,PiLp.smul_apply,
    axis_first,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem gradient_second (z : Plane) : gradient z 1=z 1/(max 1 ‖z‖) := by
  simp only [gradient,valleyGradient,radialProj,PiLp.sub_apply,PiLp.smul_apply,
    axis_second,smul_eq_mul,sub_zero,div_eq_mul_inv,mul_comm]

theorem gradient_first_nonpos (z : Plane) : gradient z 0≤0 := by
  rw [gradient_first]
  have hp : 0<max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hx : z 0≤max 1 ‖z‖ := (first_coordinate_le_norm z).trans (le_max_right _ _)
  have hh := (div_le_one hp).mpr hx
  linarith

theorem potential_outside {z : Plane} (hz : 1≤‖z‖) : potential z=‖z‖-z 0 := by
  rw [potential,valley,radialHuber_of_one_le_norm hz,inner_axis]

theorem gradient_first_outside {z : Plane} (hz : 1≤‖z‖) : gradient z 0=z 0/‖z‖-1 := by
  rw [gradient_first,max_eq_right hz]

theorem gradient_second_outside {z : Plane} (hz : 1≤‖z‖) : gradient z 1=z 1/‖z‖ := by
  rw [gradient_second,max_eq_right hz]

theorem potential_of_first_ge_two {z : Plane} (hz : 2≤z 0) :
    potential z=Real.sqrt ((z 0)^2+(z 1)^2)-z 0 := by
  have hn := first_coordinate_le_norm z
  rw [potential_outside (by linarith),norm_eq_sqrt]

theorem gradient_lipschitz : LipschitzWith 1 gradient := valleyGradient_lipschitz axis

theorem gradient_norm_le_two (z : Plane) : ‖gradient z‖≤2 :=
  valleyGradient_norm_le_two axis_norm z

theorem potential_convex : ConvexOn ℝ Set.univ potential := valley_convex axis

theorem potential_hasFDerivAt (z : Plane) :
    HasFDerivAt potential (innerSL ℝ (gradient z)) z := valley_hasFDerivAt axis z

theorem potential_hasGradientAt (z : Plane) : HasGradientAt potential (gradient z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact potential_hasFDerivAt z

theorem potential_differentiable : Differentiable ℝ potential :=
  fun z => (potential_hasFDerivAt z).differentiableAt

theorem potential_nonneg (z : Plane) : 0≤potential z := valley_nonneg axis_norm z

theorem potential_eq_zero_iff (z : Plane) : potential z=0 ↔ z 1=0 ∧ 1≤z 0 := by
  change valley axis z=0 ↔ _
  rw [valley_eq_zero_iff axis_norm]
  constructor
  · rintro ⟨t,ht,rfl⟩
    constructor
    · simp only [PiLp.smul_apply,axis_second,smul_eq_mul,mul_zero]
    · simpa only [PiLp.smul_apply,axis_first,smul_eq_mul,mul_one] using ht
  · rintro ⟨hy,hx⟩
    refine ⟨z 0,hx,?_⟩
    ext i
    fin_cases i <;> simp [axis,hy]

theorem potential_minimizers (z : Plane) :
    (∀ w, potential z≤potential w) ↔ z 1=0 ∧ 1≤z 0 := by
  rw [←potential_eq_zero_iff]
  constructor
  · intro hh
    have haxis : potential axis=0 := valley_axis_zero axis_norm
    have hl := hh axis
    rw [haxis] at hl
    exact le_antisymm hl (potential_nonneg z)
  · intro hz w
    rw [hz]
    exact potential_nonneg w

#print axioms potential_convex
#print axioms potential_hasGradientAt
#print axioms gradient_lipschitz
#print axioms gradient_norm_le_two
#print axioms potential_minimizers

end NesterovModel
