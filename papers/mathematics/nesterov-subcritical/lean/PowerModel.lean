import ConvexProjection
import PowerAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace NesterovThresholdModel

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def point (x y : ℝ) : Plane :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

@[simp] theorem point_first (x y : ℝ) : point x y 0=x := by simp [point]
@[simp] theorem point_second (x y : ℝ) : point x y 1=y := by simp [point]

theorem inner_eq (u v : Plane) : inner u v = u 0*v 0+u 1*v 1 := by
  simp only [PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,conj_trivial]
  ring

theorem norm_sq_eq (z : Plane) : ‖z‖^2=(z 0)^2+(z 1)^2 := by
  rw [←real_inner_self_eq_norm_sq,inner_eq]
  ring

noncomputable def powerSum (q : PowerExponent) (z : Plane) : ℝ :=
  (z 0+1)^q.n+(z 1)^q.n

theorem powerSum_continuous (q : PowerExponent) : Continuous (powerSum q) := by
  exact (((EuclideanSpace.proj 0 : Plane→L[ℝ]ℝ).continuous.add continuous_const).pow q.n).add
    ((EuclideanSpace.proj 1 : Plane→L[ℝ]ℝ).continuous.pow q.n)

theorem powerSum_convex (q : PowerExponent) : ConvexOn ℝ Set.univ (powerSum q) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have h0 := q.even.convexOn_pow.2 (show x 0+1∈(Set.univ:Set ℝ) from Set.mem_univ _)
    (show y 0+1∈(Set.univ:Set ℝ) from Set.mem_univ _) ha hb hab
  have h1 := q.even.convexOn_pow.2 (show x 1∈(Set.univ:Set ℝ) from Set.mem_univ _)
    (show y 1∈(Set.univ:Set ℝ) from Set.mem_univ _) ha hb hab
  simp only [smul_eq_mul] at h0 h1
  have hh : a*(x 0+1)+b*(y 0+1)=a*x 0+b*y 0+1 := by nlinarith
  rw [hh] at h0
  simp only [powerSum,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  linarith

def powerSet (q : PowerExponent) : Set Plane := {z | powerSum q z≤1}

theorem zero_mem_powerSet (q : PowerExponent) : (0:Plane)∈powerSet q := by
  simp [powerSet,powerSum,q.ne_zero]

theorem powerSet_convex (q : PowerExponent) : Convex ℝ (powerSet q) := by
  simpa only [Set.mem_univ,true_and] using (powerSum_convex q).convex_le 1

noncomputable def powerBody (q : PowerExponent) : ConvexBody Plane where
  carrier := powerSet q
  nonempty := ⟨0,zero_mem_powerSet q⟩
  closed := isClosed_le (powerSum_continuous q) continuous_const
  convex := powerSet_convex q

noncomputable def gradient (q : PowerExponent) (ε : ℝ) : Plane→Plane :=
  (powerBody q).gradient ε
noncomputable def potential (q : PowerExponent) (ε : ℝ) : Plane→ℝ :=
  (powerBody q).potential ε

 theorem gradient_mem (q : PowerExponent) (ε : ℝ) (z : Plane) :
    gradient q ε z∈powerSet q := (powerBody q).gradient_mem ε z

theorem powerSet_coords (q : PowerExponent) {g : Plane} (hg : g∈powerSet q) :
    -2≤g 0 ∧ g 0≤0 ∧ |g 1|≤1 := by
  change (g 0+1)^q.n+(g 1)^q.n≤1 at hg
  have h0 : |g 0+1|≤1 := abs_le_one_of_even_pow_le q.even q.ne_zero
    (by linarith [q.even.pow_nonneg (g 1)])
  have h1 : |g 1|≤1 := abs_le_one_of_even_pow_le q.even q.ne_zero
    (by linarith [q.even.pow_nonneg (g 0+1)])
  have hl := (abs_le.mp h0).1
  have hu := (abs_le.mp h0).2
  exact ⟨by linarith,by linarith,h1⟩

theorem gradient_first_nonpos (q : PowerExponent) (ε : ℝ) (z : Plane) :
    gradient q ε z 0≤0 := (powerSet_coords q (gradient_mem q ε z)).2.1

theorem gradient_norm_le_three (q : PowerExponent) (ε : ℝ) (z : Plane) :
    ‖gradient q ε z‖≤3 := by
  rcases powerSet_coords q (gradient_mem q ε z) with ⟨h0,h1,h2⟩
  have hl := (abs_le.mp h2).1
  have hu := (abs_le.mp h2).2
  have hn := norm_sq_eq (gradient q ε z)
  nlinarith [sq_nonneg (gradient q ε z 0+1)]

theorem potential_formula (q : PowerExponent) (ε : ℝ) (z : Plane) :
    potential q ε z=gradient q ε z 0*z 0+gradient q ε z 1*z 1
      -ε*((gradient q ε z 0)^2+(gradient q ε z 1)^2)/2 := by
  unfold potential ConvexBody.potential
  rw [inner_eq,norm_sq_eq]
  rfl

theorem potential_nonneg (q : PowerExponent) {ε : ℝ} (he : 0<ε) (z : Plane) :
    0≤potential q ε z := by
  simpa only [inner_zero_left,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,sub_self]
    using (powerBody q).dual_bound he z 0 (zero_mem_powerSet q)

theorem gradient_zero (q : PowerExponent) (ε : ℝ) : gradient q ε 0=0 := by
  unfold gradient ConvexBody.gradient
  rw [smul_zero]
  exact (powerBody q).proj_eq_self (zero_mem_powerSet q)

theorem potential_zero (q : PowerExponent) (ε : ℝ) : potential q ε 0=0 := by
  rw [potential_formula,gradient_zero]
  simp

theorem potential_initial_le_one (q : PowerExponent) {ε : ℝ} (he : 0<ε) :
    potential q ε (point 2 1)≤1 := by
  have hx := gradient_first_nonpos q ε (point 2 1)
  have hy := (powerSet_coords q (gradient_mem q ε (point 2 1))).2.2
  have hyu := (abs_le.mp hy).2
  rw [potential_formula,point_first,point_second]
  nlinarith [mul_nonneg he.le (sq_nonneg (gradient q ε (point 2 1) 0)),
    mul_nonneg he.le (sq_nonneg (gradient q ε (point 2 1) 1))]

theorem potential_convex (q : PowerExponent) {ε : ℝ} (he : 0<ε) :
    ConvexOn ℝ Set.univ (potential q ε) := (powerBody q).potential_convex he

theorem potential_hasGradientAt (q : PowerExponent) {ε : ℝ} (he : 0<ε) (z : Plane) :
    HasGradientAt (potential q ε) (gradient q ε z) z := (powerBody q).potential_hasGradientAt he z

theorem gradient_dist_le (q : PowerExponent) {ε : ℝ} (he : 0<ε) (z w : Plane) :
    ‖gradient q ε z-gradient q ε w‖≤ε⁻¹*‖z-w‖ := (powerBody q).gradient_dist_le he z w

theorem gradient_lipschitz (q : PowerExponent) {ε : ℝ} (he : 0<ε) :
    LipschitzWith ⟨ε⁻¹,le_of_lt (inv_pos.mpr he)⟩ (gradient q ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm] using gradient_dist_le q he z w

theorem gradient_variational (q : PowerExponent) {ε : ℝ} (he : 0<ε)
    (z w : Plane) (hw : w∈powerSet q) :
    inner (z-ε • gradient q ε z) (w-gradient q ε z)≤(0:ℝ) :=
  (powerBody q).gradient_variational he z w hw

end NesterovThresholdModel
