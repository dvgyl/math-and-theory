import PowerModel
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace NesterovThresholdModel

noncomputable def powerDerivative (q : PowerExponent) (g : Plane) : Plane→L[ℝ]ℝ :=
  ((q.n:ℝ)*(g 0+1)^(q.n-1)) • EuclideanSpace.proj 0 +
    ((q.n:ℝ)*(g 1)^(q.n-1)) • EuclideanSpace.proj 1

theorem powerDerivative_apply (q : PowerExponent) (g v : Plane) :
    powerDerivative q g v=(q.n:ℝ)*(g 0+1)^(q.n-1)*v 0+
      (q.n:ℝ)*(g 1)^(q.n-1)*v 1 := by rfl

theorem powerSum_hasStrictFDerivAt (q : PowerExponent) (g : Plane) :
    HasStrictFDerivAt (powerSum q) (powerDerivative q g) g := by
  exact ((hasStrictDerivAt_pow q.n (g 0+1)).comp_hasStrictFDerivAt g
    ((EuclideanSpace.proj 0 : Plane→L[ℝ]ℝ).hasStrictFDerivAt.add_const 1)).add
    ((hasStrictDerivAt_pow q.n (g 1)).comp_hasStrictFDerivAt g
      (EuclideanSpace.proj 1 : Plane→L[ℝ]ℝ).hasStrictFDerivAt)

theorem normal_boundary (q : PowerExponent) {g n : Plane} (hg : g∈powerSet q)
    (hn : ∀w∈powerSet q, inner n (w-g)≤(0:ℝ)) (hn0 : 0<n 0) : powerSum q g=1 := by
  have hle : powerSum q g≤1 := hg
  by_contra hne
  have hlt : powerSum q g<1 := lt_of_le_of_ne hle hne
  have hnhds : powerSet q∈𝓝 g := by
    filter_upwards [(powerSum_continuous q).continuousAt.eventually_lt_const hlt] with w hw
    exact hw.le
  have hm : IsMaxOn (fun w:Plane=>(inner n w:ℝ)) (powerSet q) g := by
    intro w hw
    have hh := hn w hw
    rw [inner_sub_right] at hh
    exact sub_nonpos.mp hh
  have hz := (hm.isLocalMax hnhds).hasFDerivAt_eq_zero (innerSL ℝ n).hasFDerivAt
  have hc := congrArg (fun L : Plane→L[ℝ]ℝ=>L (point 1 0)) hz
  change inner n (point 1 0)=0 at hc
  rw [inner_eq,point_first,point_second,mul_one,mul_zero,add_zero] at hc
  linarith

theorem normal_first_nonneg (q : PowerExponent) {g n : Plane} (hg : g∈powerSet q)
    (hn : ∀w∈powerSet q, inner n (w-g)≤(0:ℝ)) (hn0 : 0<n 0) : 0≤g 0+1 := by
  have href : point (-(g 0+1)-1) (g 1)∈powerSet q := by
    change powerSum q (point (-(g 0+1)-1) (g 1))≤1
    simp only [powerSum,point_first,point_second,sub_add_cancel,q.even.neg_pow]
    exact hg
  have hh := hn _ href
  rw [inner_eq] at hh
  simp only [PiLp.sub_apply,point_first,point_second,sub_self,mul_zero,add_zero] at hh
  nlinarith

/-- Every outward normal with positive first coordinate to the translated polynomial ball has the exact
power-coordinate representation. The radius is derived from Lagrange multipliers. -/
theorem normal_representation (q : PowerExponent) {g n : Plane} (hg : g∈powerSet q)
    (hn : ∀w∈powerSet q, inner n (w-g)≤(0:ℝ)) (hn0 : 0<n 0) :
    ∃R:ℝ, 0<R ∧ powerSum q g=1 ∧ 0≤g 0+1 ∧ g 0+1≤1 ∧
      n 0=R*(g 0+1)^(q.n-1) ∧ n 1=R*(g 1)^(q.n-1) := by
  have hlevel := normal_boundary q hg hn hn0
  have hh0 := normal_first_nonneg q hg hn hn0
  have hh1 : g 0+1≤1 := by have := (powerSet_coords q hg).2.1; linarith
  have hm : IsMaxOn (fun w:Plane=>(inner n w:ℝ)) {w|powerSum q w=powerSum q g} g := by
    intro w hw
    have hwmem : w∈powerSet q := by change powerSum q w≤1; rw [hw,hlevel]
    have hv := hn w hwmem
    rw [inner_sub_right] at hv
    exact sub_nonpos.mp hv
  have hextr : IsLocalExtrOn (fun w:Plane=>(inner n w:ℝ))
      {w|powerSum q w=powerSum q g} g := hm.localize.isExtr
  obtain ⟨A,B,hAB,hlin⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d
    (powerSum_hasStrictFDerivAt q g) (innerSL ℝ n).hasStrictFDerivAt
  have hqn : (q.n:ℝ)≠0 := by exact_mod_cast q.ne_zero
  have hdir : powerDerivative q g (point (g 0+1) (g 1))=q.n := by
    rw [powerDerivative_apply,point_first,point_second]
    have hs : (g 0+1)^(q.n-1)*(g 0+1)+(g 1)^(q.n-1)*g 1=1 := by
      rw [←pow_succ,←pow_succ,q.pred_succ]
      exact hlevel
    nlinarith
  have hderiv : powerDerivative q g≠0 := by
    intro hz
    have hv := congrArg (fun L:Plane→L[ℝ]ℝ=>L (point (g 0+1) (g 1))) hz
    change powerDerivative q g (point (g 0+1) (g 1))=0 at hv
    rw [hdir] at hv
    exact hqn hv
  have hB : B≠0 := by
    intro hB0
    rw [hB0,zero_smul,add_zero] at hlin
    have hA : A=0 := (smul_eq_zero.mp hlin).resolve_right hderiv
    exact hAB (by simp only [hA,hB0,Prod.zero_eq_mk])
  let R : ℝ := -A*(q.n:ℝ)/B
  have h0 : n 0=R*(g 0+1)^(q.n-1) := by
    have hh := congrArg (fun L:Plane→L[ℝ]ℝ=>L (point 1 0)) hlin
    change A*powerDerivative q g (point 1 0)+B*inner n (point 1 0)=0 at hh
    rw [powerDerivative_apply,inner_eq,point_first,point_second] at hh
    dsimp [R]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hB).mpr
    nlinarith
  have h1 : n 1=R*(g 1)^(q.n-1) := by
    have hh := congrArg (fun L:Plane→L[ℝ]ℝ=>L (point 0 1)) hlin
    change A*powerDerivative q g (point 0 1)+B*inner n (point 0 1)=0 at hh
    rw [powerDerivative_apply,inner_eq,point_first,point_second] at hh
    dsimp [R]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hB).mpr
    nlinarith
  have hp : 0<R := by
    have hpow := pow_nonneg hh0 (q.n-1)
    by_contra hnot
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hpow
    rw [←h0] at hmul
    linarith
  exact ⟨R,hp,hlevel,hh0,hh1,h0,h1⟩

end NesterovThresholdModel
