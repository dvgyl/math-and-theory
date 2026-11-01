import ActualGlobalGapStability
import RootModulusAlgebra

/-!
The exact local saturated modulus, applied to the actual finite coefficients.
No probabilistic comparison or externally supplied core data is assumed.
-/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ExactSaturatedModulus
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.GapPhaseStability
open Breakthrough.ActualGlobalGapStability Breakthrough.SharpTail

set_option maxHeartbeats 5000000

lemma finite_tail_modulus_squared {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (c : ι → ℝ) {j : ι} (hj : j ∈ T)
    (hc : ∀ i ∈ T, 0 ≤ c i) (hmax : ∀ i ∈ T, c i ≤ c j)
    (hwidth : (∑ i ∈ T, c i)^2 ≤ 2*∑ i ∈ T, (c i)^2) :
    let σ := Real.sqrt (∑ i ∈ T, (c i)^2)
    let ell := ∑ i ∈ T, c i
    2*σ*(σ-c j) ≤ (gapModulus σ (ell-σ))^2 := by
  let σ := Real.sqrt (∑ i ∈ T, (c i)^2)
  let ell := ∑ i ∈ T, c i
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ^2 = ∑ i ∈ T, (c i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hell0 : 0 ≤ ell := Finset.sum_nonneg hc
  have hVL := Finset.sum_sq_le_sq_sum_of_nonneg hc
  have hell : σ ≤ ell := by nlinarith only [hσ2, hσ0, hell0, hVL]
  have hsingle : (c j)^2 ≤ ∑ i ∈ T, (c i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg _) hj
  have hjσ : c j ≤ σ := by nlinarith only [hsingle, hσ2, hσ0, hc j hj]
  have hprod : σ^2 ≤ c j * ell := by
    rw [hσ2]
    calc
      _ ≤ ∑ i ∈ T, c j*c i := Finset.sum_le_sum (fun i hi => by
        nlinarith only [mul_le_mul_of_nonneg_right (hmax i hi) (hc i hi)])
      _ = _ := by rw [← Finset.mul_sum]
  have hs1 := Finset.add_sum_erase T c hj
  have hs2 := Finset.add_sum_erase T (fun i => (c i)^2) hj
  dsimp only at hs2
  have hrest : σ^2-(c j)^2 ≤ (ell-c j)^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := T.erase j) (f := c) (fun i hi => hc i (Finset.mem_of_mem_erase hi))
    have he : (∑ i ∈ T.erase j, c i) = ell-c j := by linarith only [hs1]
    rw [he] at h
    nlinarith only [h, hs2, hσ2]
  have ht := tail_modulus_scalar hσ0 hell hprod hrest
    (show ell^2 ≤ 2*σ^2 by nlinarith only [hwidth,hσ2])
  have hleft0 : 0 ≤ 2*σ*(σ-c j) := mul_nonneg (by positivity) (sub_nonneg.mpr hjσ)
  have hrad0 : 0 ≤ σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2)) := hleft0.trans ht
  have hrad : σ^2-2*σ*(ell-σ)-(ell-σ)^2 = 2*σ^2-ell^2 := by ring
  change 2*σ*(σ-c j) ≤ (gapModulus σ (ell-σ))^2
  unfold gapModulus
  rw [hrad]
  have hnum : σ*(σ-(ell-σ)-Real.sqrt (2*σ^2-ell^2)) =
      σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2)) := by ring
  rw [hnum,Real.sq_sqrt hrad0]
  exact ht

/-- Exact nonlinear stability on the saturated branch. The core and tail
are the actual threshold sets, and the comparison is an actual vector. -/
theorem actual_saturated_modulus_chain {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hka : ((gapCore coeff x).card : ℝ)*a^2 < 1)
    (hlocal : a-Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)-x ≤
      (Real.sqrt 2-1)*Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2))
    {j : Fin N} (hj : j ∈ gapTail coeff x)
    (hmax : ∀ i ∈ gapTail coeff x, coeff i ≤ coeff j) :
    let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
    let q := tailL1 coeff x-Real.sqrt (tailVariance coeff x)
    0 ≤ a-r-x ∧
      Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        gapModulus r q+(a-r-x-q) ∧
      Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        gapModulus r (a-r-x) := by
  let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
  let σ := Real.sqrt (tailVariance coeff x)
  let ell := tailL1 coeff x
  let κ := a-x-ell
  let Q := capDistanceSq coeff x a
  let q := ell-σ
  let e := a-r-x
  let u := κ+(σ-r)
  have hd := actual_cap_repair_data coeff hx ha hhalf hc hcap hv hg hka.le
  change 0 ≤ r ∧ r ≤ σ ∧ σ ≤ ell ∧ ell ≤ a-x ∧ 0 ≤ κ ∧
    0 ≤ capDeficit coeff x a ∧ 0 ≤ Q ∧ Q ≤ κ*capDeficit coeff x a ∧
    capDeficit coeff x a ≤ σ-r ∧ Q+(σ-r)^2 ≤ u^2 ∧
    σ^2-r^2 = 2*a*capDeficit coeff x a-Q at hd
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith only [hka])
  have hσ : 0 < σ := hr.trans_le hd.2.1
  have hσ2 : σ^2 = tailVariance coeff x :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hq : 0 ≤ q := sub_nonneg.mpr hd.2.2.1
  have hu : 0 ≤ u := add_nonneg hd.2.2.2.2.1 (sub_nonneg.mpr hd.2.1)
  have heq : e = u+q := by dsimp [e,u,κ,q]; ring
  have he : 0 ≤ e := by rw [heq]; positivity
  have hqe : q ≤ e := by rw [heq]; linarith only [hu]
  have hlocal' : e ≤ (Real.sqrt 2-1)*r := hlocal
  have hfactor : 0 ≤ Real.sqrt 2-1 := by linarith only [sqrt_two_bounds.1]
  have hqB : q ≤ (Real.sqrt 2-1)*σ :=
    (hqe.trans hlocal').trans (mul_le_mul_of_nonneg_left hd.2.1 hfactor)
  have hwidth : ell^2 ≤ 2*tailVariance coeff x := by
    have hrt2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hell0 : 0 ≤ ell := hσ.le.trans hd.2.2.1
    have hle : ell ≤ Real.sqrt 2*σ := by dsimp [q] at hqB; linarith only [hqB]
    have hs := mul_nonneg (sub_nonneg.mpr hle)
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hσ.le) hell0)
    nlinarith only [hs,hrt2,hσ2]
  have htail := finite_tail_modulus_squared (gapTail coeff x) coeff hj
    (fun i _ => hc i) hmax hwidth
  change 2*σ*(σ-coeff j) ≤ (gapModulus σ q)^2 at htail
  have hMj : coeff j ≤ σ := by
    have hj2 : (coeff j)^2 ≤ tailVariance coeff x :=
      Finset.single_le_sum (fun i _ => sq_nonneg _) hj
    nlinarith only [hj2,hσ2,hσ.le,hc j]
  have hcross := mul_nonneg (sub_nonneg.mpr hd.2.1) (sub_nonneg.mpr hMj)
  have hrepair : Q+(σ-r)^2 ≤ u^2 := hd.2.2.2.2.2.2.2.2.2.1
  have hdist : (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
      u^2+(gapModulus σ q)^2 := by
    rw [saturated_distance_identity coeff x a r hj]
    change Q+tailVariance coeff x+r^2-2*r*coeff j ≤ _
    nlinarith only [hrepair,htail,hcross,hσ2]
  have hscale := gapModulus_scale_mono hr hd.2.1 hq (hqe.trans hlocal')
  have hinc := gapModulus_increment hr hq hqe hlocal'
  have hσF : 0 ≤ gapModulus σ q := Real.sqrt_nonneg _
  have hrF : 0 ≤ gapModulus r q := Real.sqrt_nonneg _
  have heF : 0 ≤ gapModulus r e := Real.sqrt_nonneg _
  have hscale2 : (gapModulus σ q)^2 ≤ (gapModulus r q)^2 :=
    (sq_le_sq₀ hσF hrF).mpr hscale
  have hlast : u+gapModulus r q ≤ gapModulus r e := by linarith only [hinc,heq]
  have hlast2 : (u+gapModulus r q)^2 ≤ (gapModulus r e)^2 :=
    (sq_le_sq₀ (add_nonneg hu hrF) heF).mpr hlast
  have hsum2 : (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
      (gapModulus r e)^2 := by
    nlinarith only [hdist,hscale2,hlast2,mul_nonneg hu hrF]
  refine ⟨he, ?_, ?_⟩
  · have hmid2 : (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        (u+gapModulus r q)^2 := by
      nlinarith only [hdist,hscale2,mul_nonneg hu hrF]
    change Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        gapModulus r q+(e-q)
    calc
      _ ≤ Real.sqrt ((u+gapModulus r q)^2) := Real.sqrt_le_sqrt hmid2
      _ = u+gapModulus r q := Real.sqrt_sq (add_nonneg hu hrF)
      _ = gapModulus r q+(e-q) := by rw [heq]; ring
  · calc
      Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
          Real.sqrt ((gapModulus r e)^2) := Real.sqrt_le_sqrt hsum2
      _ = gapModulus r e := Real.sqrt_sq heF

theorem actual_saturated_modulus {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hka : ((gapCore coeff x).card : ℝ)*a^2 < 1)
    (hlocal : a-Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)-x ≤
      (Real.sqrt 2-1)*Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2))
    {j : Fin N} (hj : j ∈ gapTail coeff x)
    (hmax : ∀ i ∈ gapTail coeff x, coeff i ≤ coeff j) :
    let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
    0 ≤ a-r-x ∧
      Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        gapModulus r (a-r-x) := by
  have h := actual_saturated_modulus_chain coeff hx ha hhalf hc hcap hv hg hka hlocal hj hmax
  exact ⟨h.1,h.2.2⟩

lemma gapModulus_square {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hb : e ≤ (Real.sqrt 2-1)*r) :
    0 ≤ r^2-2*r*e-e^2 ∧
      (gapModulus r e)^2 = r*(r-e-Real.sqrt (r^2-2*r*e-e^2)) := by
  have hrt0 := Real.sqrt_nonneg (2 : ℝ)
  have hrt2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hprod := mul_nonneg
    (show 0 ≤ Real.sqrt 2*r-(r+e) by linarith only [hb])
    (show 0 ≤ Real.sqrt 2*r+(r+e) by positivity)
  have hrad : 0 ≤ r^2-2*r*e-e^2 := by nlinarith only [hprod,hrt2]
  have heR : e < r := by
    have h := mul_lt_mul_of_pos_right sqrt_two_bounds.2 hr
    linarith only [h,hb]
  have hroot2 := Real.sq_sqrt hrad
  have hroot0 := Real.sqrt_nonneg (r^2-2*r*e-e^2)
  have hroot : Real.sqrt (r^2-2*r*e-e^2) ≤ r-e := by
    nlinarith only [hroot2,hroot0,heR,sq_nonneg e]
  exact ⟨hrad,Real.sq_sqrt (mul_nonneg hr.le (by linarith only [hroot]))⟩

/-- Complete equality classification. The largest tail coordinate is
the explicit positive root; at most one further tail coordinate is
nonzero, and its value is the explicit negative root. -/
theorem actual_saturated_modulus_equality_iff {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hka : ((gapCore coeff x).card : ℝ)*a^2 < 1)
    (hlocal : a-Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)-x ≤
      (Real.sqrt 2-1)*Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2))
    {j : Fin N} (hj : j ∈ gapTail coeff x)
    (hmax : ∀ i ∈ gapTail coeff x, coeff i ≤ coeff j) :
    let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
    let e := a-r-x
    let d := Real.sqrt (r^2-2*r*e-e^2)
    Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) =
        gapModulus r e ↔
      (∀ i ∈ gapCore coeff x, coeff i=a) ∧ coeff j=(r+e+d)/2 ∧
      (∑ i ∈ (gapTail coeff x).erase j, coeff i)=(r+e-d)/2 ∧
      (((gapTail coeff x).erase j).filter (fun i => coeff i ≠ 0)).card ≤ 1 := by
  classical
  let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
  let σ := Real.sqrt (tailVariance coeff x)
  let ell := tailL1 coeff x
  let κ := a-x-ell
  let q := ell-σ
  let e := a-r-x
  let d := Real.sqrt (r^2-2*r*e-e^2)
  have hchain := actual_saturated_modulus_chain coeff hx ha hhalf hc hcap hv hg hka hlocal hj hmax
  change 0 ≤ e ∧
    Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
      gapModulus r q+(e-q) ∧
    Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
      gapModulus r e at hchain
  have hd := actual_cap_repair_data coeff hx ha hhalf hc hcap hv hg hka.le
  change 0 ≤ r ∧ r ≤ σ ∧ σ ≤ ell ∧ ell ≤ a-x ∧ 0 ≤ κ ∧
    0 ≤ capDeficit coeff x a ∧ 0 ≤ capDistanceSq coeff x a ∧
    capDistanceSq coeff x a ≤ κ*capDeficit coeff x a ∧
    capDeficit coeff x a ≤ σ-r ∧
    capDistanceSq coeff x a+(σ-r)^2 ≤ (κ+(σ-r))^2 ∧
    σ^2-r^2 = 2*a*capDeficit coeff x a-capDistanceSq coeff x a at hd
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith only [hka])
  have hr2 : r^2 = 1-((gapCore coeff x).card : ℝ)*a^2 :=
    Real.sq_sqrt (by linarith only [hka])
  have hσ2 : σ^2 = tailVariance coeff x :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have heq : e = κ+(σ-r)+q := by dsimp [e,κ,q]; ring
  have hq : 0 ≤ q := sub_nonneg.mpr hd.2.2.1
  have hqe : q ≤ e := by linarith only [heq,hd.2.1,hd.2.2.2.2.1]
  have hlocal' : e ≤ (Real.sqrt 2-1)*r := hlocal
  have hF := gapModulus_square hr hchain.1 hlocal'
  have hd2 : d^2 = r^2-2*r*e-e^2 := Real.sq_sqrt hF.1
  have hflatdata (hcore : ∀ i ∈ gapCore coeff x, coeff i=a) :
      capDistanceSq coeff x a=0 ∧ tailVariance coeff x=r^2 := by
    have hQ : capDistanceSq coeff x a=0 := by
      unfold capDistanceSq
      apply Finset.sum_eq_zero
      intro i hi
      rw [hcore i hi]
      norm_num
    have hC : (∑ i ∈ gapCore coeff x, (coeff i)^2) =
        ((gapCore coeff x).card : ℝ)*a^2 := by
      calc
        _ = ∑ i ∈ gapCore coeff x, a^2 := Finset.sum_congr rfl (fun i hi => by rw [hcore i hi])
        _ = _ := by simp
    have hs := core_tail_variance coeff x hv
    exact ⟨hQ,by linarith only [hs,hC,hr2]⟩
  change Real.sqrt (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) =
    gapModulus r e ↔ _
  constructor
  · intro hequal
    have hqeq : q=e := by
      by_contra hn
      have hlt : q<e := lt_of_le_of_ne hqe hn
      have hstrict := gapModulus_increment_strict hr hq hlt hlocal'
      rw [hequal] at hchain
      linarith only [hchain.2.1,hstrict]
    have hκ : κ=0 := by linarith only [heq,hqeq,hd.2.1,hd.2.2.2.2.1]
    have hσr : σ=r := by linarith only [heq,hqeq,hd.2.1,hd.2.2.2.2.1]
    have hell : ell=r+e := by dsimp [q] at hqeq; linarith only [hqeq,hσr]
    have hcore : ∀ i ∈ gapCore coeff x, coeff i=a := by
      intro i hi
      have hiL := (actual_high_gap_core coeff hx ha.le hhalf hc hcap hv hg).2.2.1 i hi
      have hκ' : a-x-tailL1 coeff x=0 := hκ
      linarith only [hiL,hκ',hcap i]
    have hFD := hflatdata hcore
    have hdist2 : (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) =
        (gapModulus r e)^2 := by
      rw [← hequal,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    rw [saturated_distance_identity coeff x a r hj,hFD.1,hFD.2,hF.2] at hdist2
    have hM : coeff j=(r+e+d)/2 := by
      change 0+r^2+r^2-2*r*coeff j=r*(r-e-d) at hdist2
      apply (mul_left_cancel₀ (ne_of_gt hr))
      linear_combination -(1/2 : ℝ)*hdist2
    have hs1 := Finset.add_sum_erase (gapTail coeff x) coeff hj
    change coeff j+(∑ i ∈ (gapTail coeff x).erase j, coeff i)=ell at hs1
    have hrest : (∑ i ∈ (gapTail coeff x).erase j, coeff i)=(r+e-d)/2 := by
      calc
        _ = ell-coeff j := by linarith only [hs1]
        _ = (r+e-d)/2 := by rw [hell,hM]; ring
    have hs2 := Finset.add_sum_erase (gapTail coeff x) (fun i => (coeff i)^2) hj
    change (coeff j)^2+(∑ i ∈ (gapTail coeff x).erase j, (coeff i)^2)=tailVariance coeff x at hs2
    have hrestsq : (∑ i ∈ (gapTail coeff x).erase j, (coeff i)^2) =
        (∑ i ∈ (gapTail coeff x).erase j, coeff i)^2 := by
      rw [hFD.2,hM] at hs2
      rw [hrest]
      linear_combination hs2-(1/2 : ℝ)*hd2
    have hsparse := (sum_sq_eq_sq_sum_iff_single ((gapTail coeff x).erase j) coeff
      (fun i _ => hc i)).mp hrestsq
    exact ⟨hcore,hM,hrest,hsparse⟩
  · rintro ⟨hcore,hM,_,_⟩
    have hFD := hflatdata hcore
    have hdist2 : (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) =
        (gapModulus r e)^2 := by
      rw [saturated_distance_identity coeff x a r hj,hFD.1,hFD.2,hF.2,hM]
      change 0+r^2+r^2-2*r*((r+e+d)/2)=r*(r-e-d)
      ring
    rw [hdist2]
    exact Real.sqrt_sq (show 0 ≤ gapModulus r e from Real.sqrt_nonneg _)

#print axioms finite_tail_modulus_squared
#print axioms actual_saturated_modulus_chain
#print axioms actual_saturated_modulus
#print axioms gapModulus_square
#print axioms actual_saturated_modulus_equality_iff

end Breakthrough.ExactSaturatedModulus
