import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Sharp finite tail concentration.  All norms below are actual finite sums. -/
noncomputable section
open scoped BigOperators
namespace Breakthrough.SharpTail

set_option maxHeartbeats 4000000

lemma normalized_tail_scalar {m s : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hs : 1 ≤ s)
    (hprod : 1 ≤ m * s)
    (hrest : 1 - m^2 ≤ (s-m)^2) :
    2 * (1-m) ≤ (2 + Real.sqrt 2) * (s-1)^2 := by
  let q : ℝ := Real.sqrt 2
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2 = 2 := Real.sq_sqrt (by norm_num)
  have hq1 : 1 < q := by nlinarith
  have hs0 : 0 < s := by linarith
  change 2 * (1-m) ≤ (2+q)*(s-1)^2
  by_cases hm : 2*m^2 ≤ 1
  · have hqm2 : (q*m)^2 ≤ 1 := by
      calc
        (q*m)^2 = q^2*m^2 := by ring
        _ = 2*m^2 := by rw [hq2]
        _ ≤ 1 := hm
    have hqm : q*m ≤ 1 := by nlinarith
    have hqs : q ≤ s := by
      have h1 := mul_le_mul_of_nonneg_left hprod hq0
      have h2 := mul_le_mul_of_nonneg_right hqm hs0.le
      nlinarith only [h1,h2]
    have hpoly : 2-q ≤ s*(s-1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqs)
        (show 0 ≤ s+q-1 by linarith)]
    have hinner : 0 ≤ (2+q)*s*(s-1)-2 := by
      have h := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 2+q by positivity)
      nlinarith only [h,hq2]
    have hmain : 0 ≤ s*((2+q)*(s-1)^2-2*(1-m)) := by
      calc
        0 ≤ (s-1)*((2+q)*s*(s-1)-2)+2*(m*s-1) :=
          add_nonneg (mul_nonneg (sub_nonneg.mpr hs) hinner)
            (by nlinarith only [hprod])
        _ = s*((2+q)*(s-1)^2-2*(1-m)) := by ring
    have hnon := nonneg_of_mul_nonneg_right hmain hs0
    linarith only [hnon]
  · have hm' : 1 ≤ 2*m^2 := le_of_lt (lt_of_not_ge hm)
    have hrad : 0 ≤ 1-m^2 := by nlinarith
    let R : ℝ := Real.sqrt (1-m^2)
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R^2 = 1-m^2 := Real.sq_sqrt hrad
    have hsm : 0 ≤ s-m := by linarith
    have hsR : m+R ≤ s := by nlinarith only [hrest,hR2,hR0,hsm]
    have hsum : 1 ≤ m+R := by nlinarith [mul_nonneg hm0 hR0]
    have htwoR : 2*R ≤ q := by nlinarith only [hm',hq2,hR2,hq0,hR0]
    have hgain : 1 ≤ (2+q)*(1-R) := by
      have h := mul_nonneg (show 0 ≤ 2+q by positivity)
        (sub_nonneg.mpr htwoR)
      nlinarith only [h,hq2]
    have hsquares : (m+R-1)^2 ≤ (s-1)^2 := by
      nlinarith only [hsR,hsum,hs]
    have hidentity : (m+R-1)^2 = 2*(1-m)*(1-R) := by
      nlinarith only [hR2]
    calc
      2*(1-m) ≤ (2+q)*(2*(1-m)*(1-R)) := by
        have h := mul_le_mul_of_nonneg_left hgain
          (show 0 ≤ 2*(1-m) by linarith)
        nlinarith only [h]
      _ = (2+q)*(m+R-1)^2 := by rw [hidentity]
      _ ≤ (2+q)*(s-1)^2 :=
        mul_le_mul_of_nonneg_left hsquares (by positivity)

lemma tail_scalar {σ M ell : ℝ}
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hMσ : M ≤ σ) (hell : σ ≤ ell)
    (hprod : σ^2 ≤ M*ell)
    (hrest : σ^2-M^2 ≤ (ell-M)^2) :
    2*σ*(σ-M) ≤ (2+Real.sqrt 2)*(ell-σ)^2 := by
  by_cases hz : σ=0
  · subst σ
    simp only [mul_zero, zero_mul, sub_zero]
    positivity
  · have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    have hm0 : 0 ≤ M/σ := div_nonneg hM hσ
    have hm1 : M/σ ≤ 1 := (div_le_one hσp).mpr hMσ
    have hs : 1 ≤ ell/σ := (one_le_div hσp).mpr hell
    have hp : 1 ≤ (M/σ)*(ell/σ) := by
      rw [div_mul_div_comm]
      apply (le_div_iff₀ (mul_pos hσp hσp)).mpr
      nlinarith only [hprod]
    have hr : 1-(M/σ)^2 ≤ (ell/σ-M/σ)^2 := by
      have hleft : 1-(M/σ)^2 = (σ^2-M^2)/σ^2 := by
        field_simp
        <;> ring
      have hright : (ell/σ-M/σ)^2 = (ell-M)^2/σ^2 := by
        rw [← sub_div, div_pow]
      rw [hleft,hright]
      exact div_le_div_of_nonneg_right hrest (sq_nonneg σ)
    have h := normalized_tail_scalar hm0 hm1 hs hp hr
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg σ)
    convert hmul using 1 <;> field_simp <;> ring

theorem sharp_tail_squared {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (j : ι) (ht : ∀ i, 0 ≤ t i)
    (hmax : ∀ i, t i ≤ t j) :
    let σ := Real.sqrt (∑ i, (t i)^2)
    let ell := ∑ i, t i
    ∑ i, (t i - if i=j then σ else 0)^2 ≤
      (2+Real.sqrt 2)*(ell-σ)^2 := by
  classical
  let σ := Real.sqrt (∑ i, (t i)^2)
  let ell := ∑ i, t i
  change (∑ i, (t i - if i=j then σ else 0)^2) ≤
      (2+Real.sqrt 2)*(ell-σ)^2
  have hS : 0 ≤ ∑ i, (t i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ^2 = ∑ i, (t i)^2 := Real.sq_sqrt hS
  have hj : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hsplit := Finset.add_sum_erase Finset.univ t hj
  have hsplit2 := Finset.add_sum_erase Finset.univ (fun i => (t i)^2) hj
  change t j + (∑ i ∈ Finset.univ.erase j, t i) = ell at hsplit
  change (t j)^2 + (∑ i ∈ Finset.univ.erase j, (t i)^2) =
      ∑ i, (t i)^2 at hsplit2
  have hterm : (t j)^2 ≤ ∑ i, (t i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (t i)) hj
  have hMσ : t j ≤ σ := by nlinarith only [hterm,hσ2,hσ0,ht j]
  have hell0 : 0 ≤ ell := Finset.sum_nonneg (fun i _ => ht i)
  have hsum : (∑ i, (t i)^2) ≤ ell^2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ht i)
  have hell : σ ≤ ell := by nlinarith only [hsum,hσ2,hσ0,hell0]
  have hprod : σ^2 ≤ t j * ell := by
    calc
      σ^2 = ∑ i, (t i)^2 := hσ2
      _ ≤ ∑ i, t j * t i := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith only [mul_le_mul_of_nonneg_right (hmax i) (ht i)]
      _ = t j * ell := by rw [← Finset.mul_sum]
  have hrest : σ^2-(t j)^2 ≤ (ell-t j)^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ.erase j) (f := t) (fun i _ => ht i)
    have he : (∑ i ∈ Finset.univ.erase j, t i) = ell-t j := by
      linarith only [hsplit]
    rw [he] at h
    linarith only [h,hsplit2,hσ2]
  have hdistance : (∑ i, (t i - if i=j then σ else 0)^2) =
      2*σ*(σ-t j) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun i => (t i-if i=j then σ else 0)^2) hj
    have he : (∑ i ∈ Finset.univ.erase j,
        (t i-if i=j then σ else 0)^2) =
        ∑ i ∈ Finset.univ.erase j, (t i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [if_neg (Finset.mem_erase.mp hi).1, sub_zero]
    rw [he] at h
    simp only [if_pos rfl] at h
    simp only [ite_true] at h
    nlinarith only [h,hsplit2,hσ2]
  rw [hdistance]
  exact tail_scalar hσ0 (ht j) hMσ hell hprod hrest

theorem sharp_tail_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (j : ι) (ht : ∀ i, 0 ≤ t i)
    (hmax : ∀ i, t i ≤ t j) :
    let σ := Real.sqrt (∑ i, (t i)^2)
    let ell := ∑ i, t i
    Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
      Real.sqrt (2+Real.sqrt 2)*(ell-σ) := by
  classical
  let σ := Real.sqrt (∑ i, (t i)^2)
  let ell := ∑ i, t i
  change Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
      Real.sqrt (2+Real.sqrt 2)*(ell-σ)
  have hS := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := t) (fun i _ => ht i)
  have hell0 : 0 ≤ ell := Finset.sum_nonneg (fun i _ => ht i)
  have hσ2 : σ^2 = ∑ i, (t i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (t i)))
  have hell : 0 ≤ ell-σ := by
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    nlinarith only [hS,hσ2,hell0,hσ0]
  have h := Real.sqrt_le_sqrt (sharp_tail_squared t j ht hmax)
  change Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
    Real.sqrt ((2+Real.sqrt 2)*(ell-σ)^2) at h
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hell] at h
  exact h

theorem two_equal_sharp :
    (∑ i : Fin 2, ((1 : ℝ)-if i=0 then Real.sqrt 2 else 0)^2) =
      (2+Real.sqrt 2)*(2-Real.sqrt 2)^2 := by
  have hq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hfac : (2+Real.sqrt 2)*(2-Real.sqrt 2) = 2 := by nlinarith only [hq]
  have he : (∑ i : Fin 2, ((1 : ℝ)-if i=0 then Real.sqrt 2 else 0)^2) =
      (1-Real.sqrt 2)^2+1 := by norm_num [Fin.sum_univ_two]
  rw [he]
  calc
    (1-Real.sqrt 2)^2+1 = 2*(2-Real.sqrt 2) := by nlinarith only [hq]
    _ = ((2+Real.sqrt 2)*(2-Real.sqrt 2))*(2-Real.sqrt 2) := by rw [hfac]
    _ = (2+Real.sqrt 2)*(2-Real.sqrt 2)^2 := by ring

#print axioms normalized_tail_scalar
#print axioms tail_scalar
#print axioms sharp_tail_squared
#print axioms sharp_tail_distance
#print axioms two_equal_sharp
end Breakthrough.SharpTail
