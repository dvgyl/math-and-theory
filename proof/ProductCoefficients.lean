module
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Exact first three coefficients of a finite product of linear factors. -/

namespace UnicyclicProduct

open scoped BigOperators
open Polynomial

variable {ι : Type*}

noncomputable def linearProduct (s : Finset ι) (x : ι → ℝ) : Polynomial ℝ :=
  ∏ i ∈ s, (1 + C (x i) * X)

theorem linear_mul_coeff_zero (a : ℝ) (P : Polynomial ℝ) :
    ((1+C a*X)*P).coeff 0 = P.coeff 0 := by
  simp [add_mul, mul_assoc, coeff_C_mul]

theorem linear_mul_coeff_succ (a : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    ((1+C a*X)*P).coeff (n+1) = P.coeff (n+1) + a*P.coeff n := by
  simp [add_mul, mul_assoc, coeff_C_mul, coeff_X_mul]

theorem linearProduct_coefficients (s : Finset ι) (x : ι → ℝ) :
    (linearProduct s x).coeff 0 = 1 ∧
    (linearProduct s x).coeff 1 = ∑ i ∈ s, x i ∧
    2*(linearProduct s x).coeff 2 =
      (∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2 ∧
    6*(linearProduct s x).coeff 3 =
      (∑ i ∈ s, x i)^3 - 3*(∑ i ∈ s, x i)*(∑ i ∈ s, (x i)^2) +
        2*(∑ i ∈ s, (x i)^3) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearProduct, coeff_one]
  | @insert a s ha ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    have hp : linearProduct (insert a s) x =
        (1+C (x a)*X)*linearProduct s x := by
      simp [linearProduct, Finset.prod_insert ha]
    rw [hp]
    simp only [linear_mul_coeff_zero, linear_mul_coeff_succ,
      Finset.sum_insert ha]
    norm_num only [Nat.reduceAdd]
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [h0, h1]
      ring
    · rw [h1]
      nlinarith only [h2]
    · have hm := congrArg (fun r : ℝ => 3*x a*r) h2
      nlinarith only [h3, hm]

theorem normalized_linearProduct_coefficients (s : Finset ι) (x : ι → ℝ)
    (hsum : ∑ i ∈ s, x i = 1) :
    (linearProduct s x).coeff 1 = 1 ∧
    (linearProduct s x).coeff 2 = (1-∑ i ∈ s, (x i)^2)/2 ∧
    (linearProduct s x).coeff 3 =
      (1-3*(∑ i ∈ s, (x i)^2)+2*(∑ i ∈ s, (x i)^3))/6 := by
  obtain ⟨_,h1,h2,h3⟩ := linearProduct_coefficients s x
  rw [hsum] at h1 h2 h3
  norm_num at h2 h3
  refine ⟨h1, ?_, ?_⟩
  · linarith only [h2]
  · linarith only [h3]

#print axioms linearProduct_coefficients
#print axioms normalized_linearProduct_coefficients

end UnicyclicProduct
