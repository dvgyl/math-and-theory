module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
The finite flow inequality used in the proposed Markov-chain argument.
The inputs are positive forward/backward stationary edge flows of common net
flux, and corrected edge increments summing to one.  The theorem proves the
claimed inequality for their quadratic form.  Identification of these objects
with arbitrary ring rates and tilted-generator cumulants is NOT assumed proved.
-/
namespace UnicyclicFiniteTUR
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem log_ratio_lower {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+1) ≤ Real.log x := by
  let f : ℝ → ℝ := fun y => Real.log y - 2*(y-1)/(y+1)
  have hd : ∀ y, 1 ≤ y →
      HasDerivAt f ((y-1)^2/(y*(y+1)^2)) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
    have hy1 : y+1 ≠ 0 := ne_of_gt (by linarith)
    have hh := (Real.hasDerivAt_log (ne_of_gt hy0)).sub
      ((((hasDerivAt_id y).sub_const 1).const_mul 2).div
        ((hasDerivAt_id y).add_const 1) hy1)
    convert hh using 1
    · funext z
      simp only [f, Pi.sub_apply, Pi.div_apply, id_eq]
    · simp only [id_eq]
      field_simp [ne_of_gt hy0, hy1] <;> ring
  have hm : MonotoneOn f (Set.Ici (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ))
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 1 ≤ y := interior_subset hy
      rw [(hd y hy').deriv]
      apply div_nonneg (sq_nonneg _)
      exact mul_nonneg (by linarith) (sq_nonneg _)
  have hh := hm (by simp : (1 : ℝ) ∈ Set.Ici (1 : ℝ)) hx hx
  simp only [f, Real.log_one, sub_self, mul_zero, zero_div, sub_zero] at hh
  linarith only [hh]

theorem flow_log_lower {a b J : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hJ : 0 < J) (hflux : a-b=J) :
    2*J/(a+b) ≤ Real.log (a/b) := by
  have hratio : 1 ≤ a/b := (le_div_iff₀ hb).mpr (by linarith)
  have hh := log_ratio_lower hratio
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hid : 2*(a/b-1)/(a/b+1) = 2*J/(a+b) := by
    rw [← hflux]
    field_simp
  rwa [hid] at hh

theorem finite_flow_tur_product {ι : Type*} [Fintype ι]
    (a b g : ι → ℝ) (J : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hJ : 0 < J) (hflux : ∀ i, a i-b i=J)
    (hg : (∑ i, g i) = 1) :
    2*J ≤ (∑ i, (a i+b i)*g i^2) *
      (∑ i, Real.log (a i/b i)) := by
  have hw : ∀ i, 0 < a i+b i := fun i => add_pos (ha i) (hb i)
  have hc2 : 0 ≤ ∑ i, (a i+b i)*g i^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)
  have hcs : 1 ≤ (∑ i, (a i+b i)*g i^2) * ∑ i, (a i+b i)⁻¹ := by
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (Finset.univ : Finset ι) (r := g)
      (f := fun i => (a i+b i)*g i^2) (g := fun i => (a i+b i)⁻¹)
      (fun i hi => mul_nonneg (le_of_lt (hw i)) (sq_nonneg _))
      (fun i hi => le_of_lt (inv_pos.mpr (hw i)))
      (fun i hi => by field_simp [ne_of_gt (hw i)])
    simpa [hg] using hh
  have hlog : 2*J*(∑ i, (a i+b i)⁻¹) ≤
      ∑ i, Real.log (a i/b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [div_eq_mul_inv] using
      flow_log_lower (ha i) (hb i) hJ (hflux i)
  have hmul := mul_le_mul_of_nonneg_left hlog hc2
  have htwoJ : 0 ≤ 2*J := by positivity
  have hmul2 := mul_le_mul_of_nonneg_left hcs htwoJ
  nlinarith only [hmul, hmul2]

theorem finite_flow_tur {ι : Type*} [Fintype ι]
    (a b g : ι → ℝ) (J : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hJ : 0 < J) (hflux : ∀ i, a i-b i=J)
    (hg : (∑ i, g i) = 1) :
    2/(∑ i, Real.log (a i/b i)) ≤
      (∑ i, (a i+b i)*g i^2)/J := by
  have hp := finite_flow_tur_product a b g J ha hb hJ hflux hg
  have hc2 : 0 ≤ ∑ i, (a i+b i)*g i^2 := by
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (le_of_lt (add_pos (ha i) (hb i))) (sq_nonneg _))
  have hA : 0 < ∑ i, Real.log (a i/b i) := by
    by_contra hn
    have hn' := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hc2 hn'
    linarith only [hp, hprod, hJ]
  exact (div_le_div_iff₀ hA hJ).mpr hp

end
end UnicyclicFiniteTUR

#print axioms UnicyclicFiniteTUR.log_ratio_lower
#print axioms UnicyclicFiniteTUR.finite_flow_tur
