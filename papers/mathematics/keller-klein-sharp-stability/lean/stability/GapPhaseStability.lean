import GlobalGapRigidity
import RootSharpTail

/-!
Quantitative stability of the exact cap optimum. All core, tail, and
comparison vectors below are obtained from the actual input coefficients.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.GapPhaseStability
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.GapMajoritySlice
open Breakthrough.HypersimplexSharp Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.SharpTail

set_option maxHeartbeats 5000000

def capDeficit {N : ℕ} (coeff : Fin N → ℝ) (x a : ℝ) : ℝ :=
  ∑ i ∈ gapCore coeff x, (a-coeff i)

def capDistanceSq {N : ℕ} (coeff : Fin N → ℝ) (x a : ℝ) : ℝ :=
  ∑ i ∈ gapCore coeff x, (a-coeff i)^2

def saturatedComparison {N : ℕ} (coeff : Fin N → ℝ) (x a r : ℝ)
    (j : Fin N) : Fin N → ℝ := by
  classical
  exact fun i => if i ∈ gapCore coeff x then a else if i=j then r else 0

lemma finite_distance_single {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (c : ι → ℝ) {j : ι} (hj : j ∈ T) (r : ℝ) :
    (∑ i ∈ T, (c i-if i=j then r else 0)^2) =
      (∑ i ∈ T, (c i)^2) + r^2-2*r*c j := by
  have h1 := Finset.add_sum_erase T (fun i => (c i-if i=j then r else 0)^2) hj
  have h2 := Finset.add_sum_erase T (fun i => (c i)^2) hj
  have hE : (∑ i ∈ T.erase j, (c i-if i=j then r else 0)^2) =
      ∑ i ∈ T.erase j, (c i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [if_neg (Finset.mem_erase.mp hi).1, sub_zero]
  rw [hE] at h1
  simp only [if_pos rfl] at h1
  dsimp only at h1 h2
  simp only [ite_true] at h1
  nlinarith only [h1, h2]

lemma finite_tail_scalar {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (c : ι → ℝ) {j : ι} (hj : j ∈ T)
    (hc : ∀ i ∈ T, 0 ≤ c i) (hmax : ∀ i ∈ T, c i ≤ c j) :
    let σ := Real.sqrt (∑ i ∈ T, (c i)^2)
    let ell := ∑ i ∈ T, c i
    2*σ*(σ-c j) ≤ (2+Real.sqrt 2)*(ell-σ)^2 := by
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
  exact tail_scalar hσ0 (hc j hj) hjσ hell hprod hrest

lemma saturated_distance_identity {N : ℕ} (coeff : Fin N → ℝ) (x a r : ℝ)
    {j : Fin N} (hj : j ∈ gapTail coeff x) :
    (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) =
      capDistanceSq coeff x a + tailVariance coeff x+r^2-2*r*coeff j := by
  classical
  let f : Fin N → ℝ := fun i => (coeff i-saturatedComparison coeff x a r j i)^2
  have hC : (∑ i ∈ gapCore coeff x, f i) = capDistanceSq coeff x a := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, saturatedComparison, if_pos hi]
    ring
  have hT : (∑ i ∈ gapTail coeff x, f i) = tailVariance coeff x+r^2-2*r*coeff j := by
    calc
      _ = ∑ i ∈ gapTail coeff x, (coeff i-if i=j then r else 0)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiC : i ∉ gapCore coeff x := (Finset.mem_sdiff.mp hi).2
        simp only [f, saturatedComparison, if_neg hiC]
      _ = _ := finite_distance_single (gapTail coeff x) coeff hj r
  have hs := Finset.sum_sdiff (Finset.subset_univ (gapCore coeff x)) (f := f)
  change (∑ i ∈ gapTail coeff x, f i)+(∑ i ∈ gapCore coeff x, f i) = ∑ i, f i at hs
  change (∑ i, f i) = _
  rw [hC, hT] at hs
  linarith only [hs]

/-- All cap-deficit repair facts, derived from the actual high-gap core. -/
theorem actual_cap_repair_data {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hka : ((gapCore coeff x).card : ℝ)*a^2 ≤ 1) :
    let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
    let σ := Real.sqrt (tailVariance coeff x)
    let ell := tailL1 coeff x
    let e := a-x-ell
    let D := capDeficit coeff x a
    let Q := capDistanceSq coeff x a
    0 ≤ r ∧ r ≤ σ ∧ σ ≤ ell ∧ ell ≤ a-x ∧ 0 ≤ e ∧ 0 ≤ D ∧ 0 ≤ Q ∧
      Q ≤ e*D ∧ D ≤ σ-r ∧ Q+(σ-r)^2 ≤ (e+(σ-r))^2 ∧
      σ^2-r^2 = 2*a*D-Q := by
  let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
  let σ := Real.sqrt (tailVariance coeff x)
  let ell := tailL1 coeff x
  let e := a-x-ell
  let D := capDeficit coeff x a
  let Q := capDistanceSq coeff x a
  have hd := actual_core_variance_data coeff hx.le ha.le hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha.le hhalf hc hcap hv hg
  have hell0 : 0 ≤ ell := hd.2.2.1
  have hellA : ell ≤ a-x := by linarith only [hs.2.2.1, hs.2.2.2.1]
  have hellhalf : ell < a/2 := by linarith only [hellA, hhalf]
  have he0 : 0 ≤ e := by dsimp [e]; linarith only [hellA]
  have heA : e ≤ a := by dsimp [e]; linarith only [hx, hell0]
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ^2 = tailVariance coeff x := Real.sq_sqrt hd.1
  have hσell : σ ≤ ell := by nlinarith only [hd.2.2.2.1, hσ2, hσ0, hell0]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = 1-((gapCore coeff x).card : ℝ)*a^2 := Real.sq_sqrt (by linarith)
  have hrσ : r ≤ σ := by nlinarith only [hr2, hσ2, hd.2.2.2.2.2, hr0, hσ0]
  have hdiff : 0 ≤ σ-r := sub_nonneg.mpr hrσ
  have hsumA : σ+r ≤ a := by linarith only [hrσ, hσell, hellhalf]
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hcap i))
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : Q ≤ e*D := by
    calc
      Q ≤ ∑ i ∈ gapCore coeff x, e*(a-coeff i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi0 := sub_nonneg.mpr (hcap i)
        have hicut := (actual_high_gap_core coeff hx ha.le hhalf hc hcap hv hg).2.2.1 i hi
        have hie : a-coeff i ≤ e := by dsimp [e, ell]; linarith only [hicut]
        nlinarith only [mul_le_mul_of_nonneg_right hie hi0]
      _ = e*D := by rw [← Finset.mul_sum]; rfl
  have henergy : σ^2-r^2 = 2*a*D-Q := by
    have hp : ∀ i, (coeff i)^2 = a^2-2*a*(a-coeff i)+(a-coeff i)^2 := by intro i; ring
    have hsum := core_tail_variance coeff x hv
    simp_rw [hp] at hsum
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hDS : ((gapCore coeff x).card : ℝ)*a-(∑ i ∈ gapCore coeff x, coeff i) = D := by
      dsimp [D, capDeficit]
      rw [Finset.sum_sub_distrib]
      simp
    rw [hDS] at hsum
    change ((gapCore coeff x).card : ℝ)*a^2-2*a*D+Q+tailVariance coeff x = 1 at hsum
    nlinarith only [hsum, hσ2, hr2]
  have hDdiff : D ≤ σ-r := by
    apply (mul_le_mul_left ha).mp
    have hQA := mul_le_mul_of_nonneg_right heA hD0
    have hp := mul_le_mul_of_nonneg_left hsumA hdiff
    nlinarith only [henergy, hQ, hQA, hp]
  have hrepair : Q+(σ-r)^2 ≤ (e+(σ-r))^2 := by
    have hQD := mul_le_mul_of_nonneg_left hDdiff he0
    have heD := mul_nonneg he0 hdiff
    nlinarith only [hQ, hQD, heD, sq_nonneg e]
  exact ⟨hr0, hrσ, hσell, hellA, he0, hD0, hQ0, hQ, hDdiff, hrepair, henergy⟩

/-- Stability on the saturated branch, with an actual largest tail
coordinate and the actual finite comparison vector. -/
theorem actual_saturated_stability {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hka : ((gapCore coeff x).card : ℝ)*a^2 ≤ 1)
    {j : Fin N} (hj : j ∈ gapTail coeff x)
    (hmax : ∀ i ∈ gapTail coeff x, coeff i ≤ coeff j) :
    let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
    0 ≤ a-r-x ∧
      (∑ i, (coeff i-saturatedComparison coeff x a r j i)^2) ≤
        (2+Real.sqrt 2)*(a-r-x)^2 := by
  let r := Real.sqrt (1-((gapCore coeff x).card : ℝ)*a^2)
  let σ := Real.sqrt (tailVariance coeff x)
  let ell := tailL1 coeff x
  let e := a-x-ell
  let D := capDeficit coeff x a
  let Q := capDistanceSq coeff x a
  have hd := actual_core_variance_data coeff hx.le ha.le hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha.le hhalf hc hcap hv hg
  have hell0 : 0 ≤ ell := hd.2.2.1
  have hellA : ell ≤ a-x := by linarith only [hs.2.2.1, hs.2.2.2.1]
  have hellhalf : ell < a/2 := by linarith only [hellA, hhalf]
  have he0 : 0 ≤ e := by dsimp [e]; linarith only [hellA]
  have heA : e ≤ a := by dsimp [e]; linarith only [hx, hell0]
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ^2 = tailVariance coeff x := Real.sq_sqrt hd.1
  have hσell : σ ≤ ell := by nlinarith only [hd.2.2.2.1, hσ2, hσ0, hell0]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = 1-((gapCore coeff x).card : ℝ)*a^2 := Real.sq_sqrt (by linarith)
  have hrσ : r ≤ σ := by nlinarith only [hr2, hσ2, hd.2.2.2.2.2, hr0, hσ0]
  have hdiff : 0 ≤ σ-r := sub_nonneg.mpr hrσ
  have hsumA : σ+r ≤ a := by linarith only [hrσ, hσell, hellhalf]
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hcap i))
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : Q ≤ e*D := by
    calc
      Q ≤ ∑ i ∈ gapCore coeff x, e*(a-coeff i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi0 := sub_nonneg.mpr (hcap i)
        have hicut := (actual_high_gap_core coeff hx ha.le hhalf hc hcap hv hg).2.2.1 i hi
        have hie : a-coeff i ≤ e := by dsimp [e, ell]; linarith only [hicut]
        nlinarith only [mul_le_mul_of_nonneg_right hie hi0]
      _ = e*D := by rw [← Finset.mul_sum]; rfl
  have henergy : σ^2-r^2 = 2*a*D-Q := by
    have hp : ∀ i, (coeff i)^2 = a^2-2*a*(a-coeff i)+(a-coeff i)^2 := by intro i; ring
    have hsum := core_tail_variance coeff x hv
    simp_rw [hp] at hsum
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hDS : ((gapCore coeff x).card : ℝ)*a-(∑ i ∈ gapCore coeff x, coeff i) = D := by
      dsimp [D, capDeficit]
      rw [Finset.sum_sub_distrib]
      simp
    rw [hDS] at hsum
    change ((gapCore coeff x).card : ℝ)*a^2-2*a*D+Q+tailVariance coeff x = 1 at hsum
    nlinarith only [hsum, hσ2, hr2]
  have hDdiff : D ≤ σ-r := by
    apply (mul_le_mul_left ha).mp
    have hQA := mul_le_mul_of_nonneg_right heA hD0
    have hp := mul_le_mul_of_nonneg_left hsumA hdiff
    nlinarith only [henergy, hQ, hQA, hp]
  have hrepair : Q+(σ-r)^2 ≤ (e+(σ-r))^2 := by
    have hQD := mul_le_mul_of_nonneg_left hDdiff he0
    have heD := mul_nonneg he0 hdiff
    nlinarith only [hQ, hQD, heD, sq_nonneg e]
  have htail := finite_tail_scalar (gapTail coeff x) coeff hj (fun i _ => hc i) hmax
  change 2*σ*(σ-coeff j) ≤ (2+Real.sqrt 2)*(ell-σ)^2 at htail
  have hMj : coeff j ≤ σ := by
    have hj2 : (coeff j)^2 ≤ tailVariance coeff x :=
      Finset.single_le_sum (fun i _ => sq_nonneg _) hj
    nlinarith only [hj2, hσ2, hσ0, hc j]
  have hcross := mul_nonneg hdiff (sub_nonneg.mpr hMj)
  have hdist : Q+tailVariance coeff x+r^2-2*r*coeff j ≤
      (e+(σ-r))^2+(2+Real.sqrt 2)*(ell-σ)^2 := by
    nlinarith only [hrepair, htail, hcross, hσ2]
  have hU : 0 ≤ e+(σ-r) := add_nonneg he0 hdiff
  have hW : 0 ≤ ell-σ := sub_nonneg.mpr hσell
  have hcoef : 1 ≤ 2+Real.sqrt 2 := by linarith only [Real.sqrt_nonneg (2 : ℝ)]
  have hsq := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (e+(σ-r)))
  have hpos := mul_nonneg (show 0 ≤ 2+Real.sqrt 2 by positivity) (mul_nonneg hU hW)
  have hbudget : (e+(σ-r))+(ell-σ) = a-r-x := by dsimp [e]; ring
  refine ⟨by linarith only [hU, hW, hbudget], ?_⟩
  rw [saturated_distance_identity coeff x a r hj]
  change Q+tailVariance coeff x+r^2-2*r*coeff j ≤ _
  have hb : (e+(σ-r))^2+(2+Real.sqrt 2)*(ell-σ)^2 ≤
      (2+Real.sqrt 2)*((e+(σ-r))+(ell-σ))^2 := by
    nlinarith only [hsq, hpos]
  rw [hbudget] at hb
  exact hdist.trans hb

#print axioms actual_cap_repair_data
#print axioms finite_tail_scalar
#print axioms saturated_distance_identity
#print axioms actual_saturated_stability

end Breakthrough.GapPhaseStability
