import RootSharpTail
import ExactSupportGapEquality

/-! The exact two-coordinate tail modulus, with actual finite-vector realization. -/
noncomputable section
open scoped BigOperators
namespace Breakthrough.SharpTail

set_option maxHeartbeats 4000000

lemma tail_modulus_scalar {σ M ell : ℝ}
    (hσ : 0 ≤ σ) (hell : σ ≤ ell)
    (hprod : σ^2 ≤ M*ell)
    (hrest : σ^2-M^2 ≤ (ell-M)^2)
    (hwidth : ell^2 ≤ 2*σ^2) :
    2*σ*(σ-M) ≤ σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2)) := by
  by_cases hz : σ=0
  · simp only [hz,zero_mul,mul_zero]
    exact le_rfl
  · have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    have hellp : 0 < ell := lt_of_lt_of_le hσp hell
    have hhalf : ell ≤ 2*M := by
      by_contra hn
      have hpos := mul_pos hellp (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hpos,hprod,hwidth]
    have hroot0 : 0 ≤ Real.sqrt (2*σ^2-ell^2) := Real.sqrt_nonneg _
    have hroot2 : (Real.sqrt (2*σ^2-ell^2))^2 = 2*σ^2-ell^2 :=
      Real.sq_sqrt (by linarith only [hwidth])
    have hroot : Real.sqrt (2*σ^2-ell^2) ≤ 2*M-ell := by
      nlinarith only [hrest,hhalf,hroot0,hroot2]
    have hm := mul_le_mul_of_nonneg_left hroot hσ
    nlinarith only [hm]

theorem exact_tail_modulus_squared {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (j : ι) (ht : ∀ i, 0 ≤ t i)
    (hmax : ∀ i, t i ≤ t j)
    (hwidth : (∑ i, t i)^2 ≤ 2*∑ i, (t i)^2) :
    let σ := Real.sqrt (∑ i, (t i)^2)
    let ell := ∑ i, t i
    ∑ i, (t i-if i=j then σ else 0)^2 ≤
      σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2)) := by
  classical
  let σ := Real.sqrt (∑ i, (t i)^2)
  let ell := ∑ i, t i
  change (∑ i, (t i-if i=j then σ else 0)^2) ≤
      σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2))
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ^2 = ∑ i, (t i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (t i)))
  have hell0 : 0 ≤ ell := Finset.sum_nonneg (fun i _ => ht i)
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := t) (fun i _ => ht i)
  have hell : σ ≤ ell := by nlinarith only [hσ2,hell0,hσ0,hsum]
  have hprod : σ^2 ≤ t j * ell := by
    calc
      σ^2 = ∑ i, (t i)^2 := hσ2
      _ ≤ ∑ i, t j * t i := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith only [mul_le_mul_of_nonneg_right (hmax i) (ht i)]
      _ = t j * ell := by rw [← Finset.mul_sum]
  have hj : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hsplit := Finset.add_sum_erase Finset.univ t hj
  have hsplit2 := Finset.add_sum_erase Finset.univ (fun i => (t i)^2) hj
  change t j + (∑ i ∈ Finset.univ.erase j, t i) = ell at hsplit
  change (t j)^2 + (∑ i ∈ Finset.univ.erase j, (t i)^2) =
      ∑ i, (t i)^2 at hsplit2
  have hrest : σ^2-(t j)^2 ≤ (ell-t j)^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ.erase j) (f := t) (fun i _ => ht i)
    have he : (∑ i ∈ Finset.univ.erase j, t i) = ell-t j := by
      linarith only [hsplit]
    rw [he] at h
    linarith only [h,hsplit2,hσ2]
  have hdistance : (∑ i, (t i-if i=j then σ else 0)^2) =
      2*σ*(σ-t j) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun i => (t i-if i=j then σ else 0)^2) hj
    have he : (∑ i ∈ Finset.univ.erase j,
        (t i-if i=j then σ else 0)^2) =
        ∑ i ∈ Finset.univ.erase j, (t i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [if_neg (Finset.mem_erase.mp hi).1,sub_zero]
    rw [he] at h
    simp only [if_pos rfl,ite_true] at h
    nlinarith only [h,hsplit2,hσ2]
  rw [hdistance]
  exact tail_modulus_scalar hσ0 hell hprod hrest (by nlinarith only [hwidth,hσ2])

#print axioms tail_modulus_scalar
#print axioms exact_tail_modulus_squared
end Breakthrough.SharpTail
