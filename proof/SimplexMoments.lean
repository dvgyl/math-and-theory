module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Finite-simplex moment inequalities and the algebraic upper skewness bound.
This file does not identify the scalar expression with a Markov-current
cumulant; that spectral and probabilistic bridge is a separate obligation.
-/

namespace UnicyclicSimplex

open scoped BigOperators

variable {ι : Type*}

theorem third_elementary_nonneg (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ (∑ i ∈ s, x i)^3 -
      3 * (∑ i ∈ s, x i) * (∑ i ∈ s, (x i)^2) +
      2 * (∑ i ∈ s, (x i)^3) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hprev := ih hxs
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hxs
    have hprod : 0 ≤ 3 * x a *
        ((∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
    simp only [Finset.sum_insert ha]
    nlinarith only [hprev, hprod]

theorem simplex_second_moment_le_one (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hsum : ∑ i ∈ s, x i = 1) :
    (∑ i ∈ s, (x i)^2) ≤ 1 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg hx
  simpa only [hsum, one_pow] using h

theorem simplex_third_relation (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hsum : ∑ i ∈ s, x i = 1) :
    0 ≤ 1 - 3 * (∑ i ∈ s, (x i)^2) + 2 * (∑ i ∈ s, (x i)^3) := by
  simpa only [hsum, one_pow, mul_one] using third_elementary_nonneg s x hx

theorem sum_cubes_le_sqrt_second_cube (s : Finset ι) (x : ι → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (hx : ∀ i ∈ s, 0 ≤ x i)
    (htsq : ∑ i ∈ s, (x i)^2 = t^2) :
    (∑ i ∈ s, (x i)^3) ≤ t^3 := by
  have hpoint : ∀ i ∈ s, (x i)^3 ≤ t * (x i)^2 := by
    intro i hi
    have hxi := hx i hi
    have hsqi : (x i)^2 ≤ t^2 := by
      rw [← htsq]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) hi
    have hle : x i ≤ t := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg (x i))
    nlinarith only [hmul]
  calc
    (∑ i ∈ s, (x i)^3) ≤ ∑ i ∈ s, t * (x i)^2 :=
      Finset.sum_le_sum hpoint
    _ = t * ∑ i ∈ s, (x i)^2 := by rw [Finset.mul_sum]
    _ = t^3 := by rw [htsq]; ring

theorem skewness_upper_scalar (p2 p3 c2 : ℝ)
    (hc2 : 0 ≤ c2) (hp2 : p2 ≤ 1)
    (he3 : 0 ≤ 1 - 3*p2 + 2*p3)
    (hvar : 0 ≤ (1-c2)/2 + p2*c2) :
    c2 * (3*p2^2 - 2*p3) + (c2-1)*(1-3*p2)/2 ≤ 1 := by
  let e2 := (1-p2)/2
  have he2 : 0 ≤ e2 := by dsimp [e2]; linarith
  have hbound : 4*c2*e2 ≤ c2+1 := by dsimp [e2]; nlinarith only [hvar]
  have hprod := mul_le_mul_of_nonneg_right hbound he2
  have he3prod := mul_nonneg hc2 he3
  dsimp [e2] at hprod
  nlinarith only [hprod, he3prod]

theorem skewness_upper_simplex (s : Finset ι) (x : ι → ℝ) (c : ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hsum : ∑ i ∈ s, x i = 1)
    (hvar : 0 ≤ (1-c^2)/2 + (∑ i ∈ s, (x i)^2)*c^2) :
    c^2 * (3*(∑ i ∈ s, (x i)^2)^2 - 2*(∑ i ∈ s, (x i)^3)) +
      (c^2-1)*(1-3*(∑ i ∈ s, (x i)^2))/2 ≤ 1 := by
  exact skewness_upper_scalar _ _ _ (sq_nonneg c)
    (simplex_second_moment_le_one s x hx hsum)
    (simplex_third_relation s x hx hsum) hvar

#print axioms third_elementary_nonneg
#print axioms sum_cubes_le_sqrt_second_cube
#print axioms skewness_upper_simplex

end UnicyclicSimplex
