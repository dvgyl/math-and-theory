module

public import MathAndTheory.Mathematics.Gyires.FourBlock
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open scoped BigOperators
open Finset Polynomial
open MathAndTheory.Gyires.Bernoulli

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def oneSuccess (u : ι → ℝ) : ℝ :=
  ∑ i, u i * ∏ j ∈ Finset.univ.erase i, (1-u j)

noncomputable def secondMoment (u : ι → ℝ) : ℝ := ∑ i, u i^2

lemma oneSuccess_nonneg (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1) : 0 ≤ oneSuccess u := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hu.1 i)
  apply Finset.prod_nonneg
  intro j hj
  exact sub_nonneg.mpr (hu.2 j)

omit [Fintype ι] in
lemma one_sub_sum_le_product (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1) (s : Finset ι) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1-u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hu.2 i))
    simp only [Pi.one_apply] at hm
    have hs : 0 ≤ ∑ j ∈ s, u j := Finset.sum_nonneg (fun j hj => hu.1 j)
    nlinarith [mul_nonneg (hu.1 i) hs]

theorem secondMoment_le_oneSuccess (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) : secondMoment u ≤ oneSuccess u := by
  apply Finset.sum_le_sum
  intro i hi
  have hprod := one_sub_sum_le_product u hu (Finset.univ.erase i)
  have hs := Finset.sum_erase_add Finset.univ (fun j => u j) (Finset.mem_univ i)
  rw [hsum] at hs
  have h : u i ≤ ∏ j ∈ Finset.univ.erase i, (1-u j) := by linarith
  simpa only [pow_two] using mul_le_mul_of_nonneg_left h (hu.1 i)

lemma oneSuccess_eq_probability (u : ι → ℝ) : oneSuccess u = probability u 1 := by
  have he : (derivative (generating u)).eval 0 = oneSuccess u := by
    unfold generating
    rw [derivative_prod_finset, eval_finsetSum]
    simp only [derivative_add, derivative_C, derivative_mul, derivative_X,
      zero_mul, mul_zero, zero_add, add_zero, mul_one, eval_mul, eval_add, eval_X, eval_C, eval_prod]
    unfold oneSuccess
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← generating_coeff]
  rw [← he, ← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

omit [DecidableEq ι] in
lemma secondMoment_bounds (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (hn : 0 < Fintype.card ι) :
    1 / (Fintype.card ι : ℝ) ≤ secondMoment u ∧ secondMoment u ≤ 1 := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hs : 0 ≤ ∑ i, (u i - 1 / (Fintype.card ι : ℝ))^2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hexpand : (∑ i, (u i - 1 / (Fintype.card ι : ℝ))^2) =
      secondMoment u - 1 / (Fintype.card ι : ℝ) := by
    have ht (i : ι) : (u i - 1 / (Fintype.card ι : ℝ))^2 =
        u i^2 - (2 / (Fintype.card ι : ℝ)) * u i + (1 / (Fintype.card ι : ℝ))^2 := by ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, secondMoment]
    field_simp
    ring
  rw [hexpand] at hs
  refine ⟨by linarith, ?_⟩
  calc
    secondMoment u ≤ ∑ i, u i := by
      apply Finset.sum_le_sum
      intro i hi
      have h0 : 0 ≤ u i := hu.1 i
      have h1 : u i ≤ 1 := hu.2 i
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    _ = 1 := hsum

lemma convex_entropy_remainder :
    ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) (fun x => x * Real.log x - x^2/2) := by
  have hc : ContinuousOn (fun x : ℝ => x * Real.log x - x^2/2) (Set.Ioc 0 1) := by
    intro x hx
    exact ((continuousAt_id.mul (Real.continuousAt_log hx.1.ne')).sub
      ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 1) hc
    (f' := fun x => Real.log x + 1 - x) (f'' := fun x => x⁻¹ - 1)
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa using hx
    have hd : HasDerivAt (fun y : ℝ => y * Real.log y - y^2/2) (Real.log x + 1 - x) x := by
      convert (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx'.1.ne')).sub
        (((hasDerivAt_id x).pow 2).div_const 2)) using 1
      · rfl
      · dsimp
        field_simp [hx'.1.ne']
    exact hd.hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa using hx
    exact (((Real.hasDerivAt_log hx'.1.ne').add_const 1).sub (hasDerivAt_id x)).hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa using hx
    have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hx'.1).mpr hx'.2.le
    linarith

lemma log_oneSuccess_lower (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (hint : ∀ i, u i < 1) :
    (∑ i, (1-u i) * Real.log (1-u i)) ≤ Real.log (oneSuccess u) := by
  let z : ι → ℝ := fun i => ∏ j ∈ Finset.univ.erase i, (1-u j)
  have hz (i : ι) : 0 < z i := by
    apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hint j)
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := u) (p := z) (fun i hi => hu.1 i) hsum
    (fun i hi => hz i)
  have hl (i : ι) : Real.log (z i) = ∑ j ∈ Finset.univ.erase i, Real.log (1-u j) := by
    exact Real.log_prod (fun j hj => (sub_pos.mpr (hint j)).ne')
  have he : (∑ i, u i * Real.log (z i)) = ∑ i, (1-u i) * Real.log (1-u i) := by
    simp_rw [hl]
    have hs (i : ι) : (∑ j ∈ Finset.univ.erase i, Real.log (1-u j)) =
        (∑ j, Real.log (1-u j)) - Real.log (1-u i) := by
      exact Finset.sum_erase_eq_sub (Finset.mem_univ i)
    simp_rw [hs, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
  change (∑ i, u i * Real.log (z i)) ≤ Real.log (oneSuccess u) at hj
  rwa [he] at hj

omit [DecidableEq ι] in
theorem entropy_lower (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (hint : ∀ i, u i < 1) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * (1-1/(Fintype.card ι : ℝ)) *
      Real.log (1-1/(Fintype.card ι : ℝ)) +
        (secondMoment u - 1/(Fintype.card ι : ℝ))/2 ≤
          ∑ i, (1-u i)*Real.log (1-u i) := by
  let N : ℝ := Fintype.card ι
  let t : ℝ := 1-1/N
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hscale : N*(1/N) = 1 := by field_simp
  have hw : (∑ _ : ι, (1/N)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hscale
  have hv : (∑ i, (1-u i)) = N-1 := by simp [N, Finset.sum_sub_distrib, hsum]
  have hm : (∑ i, (1/N)*(1-u i)) = t := by
    rw [← Finset.mul_sum, hv]
    dsimp [t]
    field_simp
  have hv2 : (∑ i, (1-u i)^2) = N-2+secondMoment u := by
    have ht (i : ι) : (1-u i)^2 = 1-2*u i+u i^2 := by ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum, hsum]
    dsimp [N, secondMoment]
  have hj := convex_entropy_remainder.map_sum_le (t := Finset.univ)
    (w := fun _ : ι => 1/N) (p := fun i => 1-u i) (fun i hi => by positivity) hw
    (fun i hi => ⟨sub_pos.mpr (hint i), sub_le_self 1 (hu.1 i)⟩)
  simp only [smul_eq_mul, hm] at hj
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, hv2] at hj
  have hmj := mul_le_mul_of_nonneg_left hj hN.le
  simp only [← mul_assoc, hscale, one_mul] at hmj
  have ht2 : N*t^2 = N-2+1/N := by
    dsimp [t]
    field_simp
    ring
  change N*t*Real.log t + (secondMoment u-1/N)/2 ≤ _
  nlinarith [ht2]

theorem log_oneSuccess_refined (u : ι → ℝ) (hu : u ∈ Set.Icc 0 1)
    (hsum : ∑ i, u i = 1) (hint : ∀ i, u i < 1) (k : ℕ)
    (hcard : Fintype.card ι = k+2) :
    2*((k : ℝ)+1)*Real.log (((k : ℝ)+1)/((k : ℝ)+2)) +
      (secondMoment u - 1/((k : ℝ)+2)) ≤ 2*Real.log (oneSuccess u) := by
  have he := entropy_lower u hu hsum hint (by omega : 0 < Fintype.card ι)
  have hl := log_oneSuccess_lower u hu hsum hint
  rw [hcard] at he
  push_cast at he
  have ht : 1-1/((k : ℝ)+2) = ((k : ℝ)+1)/((k : ℝ)+2) := by field_simp; ring
  rw [ht] at he
  have hm : ((k : ℝ)+2) * (((k : ℝ)+1)/((k : ℝ)+2)) = (k : ℝ)+1 := by field_simp
  rw [hm] at he
  linarith

lemma oneSuccess_const (q : ℝ) : oneSuccess (fun _ : ι => q) =
    (Fintype.card ι : ℝ) * q * (1-q)^(Fintype.card ι-1) := by
  simp [oneSuccess, mul_assoc]


end MathAndTheory.Gyires.Exceptional
