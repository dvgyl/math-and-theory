import BookDomination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
open Polynomial
open SquareFlowerCompletion.Counting
namespace BookCompletion
attribute [local instance] Classical.propDecidable

def pairGF : P := ∑ b : Branch, pairWeight b
def nonemptyGF : P := ∑ b : Branch, if pairNonempty b then pairWeight b else 0

theorem pairGF_eq : pairGF = ((1 : P)+X)^2 := by
  simp [pairGF, pairWeight, bitWeight, Fintype.sum_prod_type]
  ring

theorem nonemptyGF_eq : nonemptyGF = (X : P)^2+2*X := by
  simp [nonemptyGF, pairWeight, bitWeight, pairNonempty, Fintype.sum_prod_type]
  ring

theorem noFirstGF_eq :
    (∑ b : Branch, if pairNonempty b ∧ b.1≠true then pairWeight b else 0) = (X : P) := by
  simp [pairWeight, bitWeight, pairNonempty, Fintype.sum_prod_type]

theorem noLastGF_eq :
    (∑ b : Branch, if pairNonempty b ∧ b.2≠true then pairWeight b else 0) = (X : P) := by
  simp [pairWeight, bitWeight, pairNonempty, Fintype.sum_prod_type]

theorem neitherGF_eq :
    (∑ b : Branch, if pairNonempty b ∧ b.1≠true ∧ b.2≠true then pairWeight b else 0) = (0 : P) := by
  simp [pairWeight, bitWeight, pairNonempty, Fintype.sum_prod_type]

theorem all_pair_sum (n : ℕ) :
    (∑ b : Fin n → Branch, ∏ i, pairWeight (b i)) = pairGF^n := by
  exact (Fintype.sum_pow pairWeight n).symm

theorem all_nonempty_sum (n : ℕ) :
    (∑ b : Fin n → Branch,
      if ∀ i, pairNonempty (b i) then ∏ i, pairWeight (b i) else 0) = nonemptyGF^n :=
  weighted_product_sum n pairNonempty pairWeight

theorem all_noFirst_sum (n : ℕ) :
    (∑ b : Fin n → Branch,
      if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).1=true)
      then ∏ i, pairWeight (b i) else 0) = (X : P)^n := by
  have h := weighted_product_sum n (fun b : Branch => pairNonempty b ∧ b.1≠true) pairWeight
  conv at h =>
    rhs
    simp [pairNonempty, pairWeight, bitWeight, Fintype.sum_prod_type]
  simpa only [forall_and, not_exists] using h

theorem all_noLast_sum (n : ℕ) :
    (∑ b : Fin n → Branch,
      if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).2=true)
      then ∏ i, pairWeight (b i) else 0) = (X : P)^n := by
  have h := weighted_product_sum n (fun b : Branch => pairNonempty b ∧ b.2≠true) pairWeight
  conv at h =>
    rhs
    simp [pairNonempty, pairWeight, bitWeight, Fintype.sum_prod_type]
  simpa only [forall_and, not_exists] using h

theorem all_neither_sum (n : ℕ) :
    (∑ b : Fin n → Branch,
      if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).1=true) ∧ (¬ ∃ i, (b i).2=true)
      then ∏ i, pairWeight (b i) else 0) = (0 : P)^n := by
  have h := weighted_product_sum n
    (fun b : Branch => pairNonempty b ∧ b.1≠true ∧ b.2≠true) pairWeight
  conv at h =>
    rhs
    simp [pairNonempty, pairWeight, bitWeight, Fintype.sum_prod_type]
  simpa only [forall_and, not_exists] using h

def noHubsGF (n : ℕ) : P := ∑ b : Fin n → Branch,
  if (∀ i, pairNonempty (b i)) ∧ (∃ i, (b i).1=true) ∧ (∃ i, (b i).2=true)
    then ∏ i, pairWeight (b i) else 0

theorem noHubsGF_eq (n : ℕ) :
    noHubsGF n = nonemptyGF^n - (X : P)^n - X^n + (0 : P)^n := by
  have split (b : Fin n → Branch) :
      (if (∀ i, pairNonempty (b i)) ∧ (∃ i, (b i).1=true) ∧ (∃ i, (b i).2=true)
        then ∏ i, pairWeight (b i) else 0) =
      (if ∀ i, pairNonempty (b i) then ∏ i, pairWeight (b i) else 0) -
      (if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).1=true)
        then ∏ i, pairWeight (b i) else 0) -
      (if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).2=true)
        then ∏ i, pairWeight (b i) else 0) +
      (if (∀ i, pairNonempty (b i)) ∧ (¬ ∃ i, (b i).1=true) ∧ (¬ ∃ i, (b i).2=true)
        then ∏ i, pairWeight (b i) else 0) := by
    by_cases ha : ∀ i, pairNonempty (b i) <;>
      by_cases hu : ∃ i, (b i).1=true <;>
      by_cases hv : ∃ i, (b i).2=true <;> simp [ha,hu,hv]
  unfold noHubsGF
  simp_rw [split]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    all_nonempty_sum, all_noFirst_sum, all_noLast_sum, all_neither_sum]

def hubsGF (n : ℕ) : P := ∑ h : Branch, ∑ b : Fin n → Branch,
  if valid (h,b) then pairWeight h * ∏ i, pairWeight (b i) else 0

theorem hubsGF_factor (n : ℕ) :
    hubsGF n = (X : P)^2 * pairGF^n + 2*X*nonemptyGF^n + noHubsGF n := by
  have single_sum :
      (∑ b : Fin n → Branch,
        if ∀ i, pairNonempty (b i) then X * ∏ i, pairWeight (b i) else 0) =
        (X : P) * nonemptyGF^n := by
    rw [← all_nonempty_sum n, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : ∀ i, pairNonempty (b i) <;> simp [h]
  have double_sum :
      (∑ b : Fin n → Branch, (X : P)*X * ∏ i, pairWeight (b i)) = X^2*pairGF^n := by
    rw [← all_pair_sum n, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have wtt : pairWeight (true,true) = (X : P)*X := by simp [pairWeight, bitWeight]
  have wtf : pairWeight (true,false) = (X : P) := by simp [pairWeight, bitWeight]
  have wft : pairWeight (false,true) = (X : P) := by simp [pairWeight, bitWeight]
  have wff : pairWeight (false,false) = (1 : P) := by simp [pairWeight, bitWeight]
  simp only [hubsGF, Fintype.sum_prod_type, Fintype.sum_bool, valid, branchValid,
    Bool.false_eq_true, false_or, true_or, true_and, and_true,
    ite_true, ite_false, one_mul, and_self, forall_true_iff, wtt, wtf, wft, wff]
  simp only [single_sum, double_sum]
  change ((X : P)^2*pairGF^n + X*nonemptyGF^n) + (X*nonemptyGF^n + noHubsGF n) = _
  ring

theorem dominationPolynomial_eq_hubsGF (n : ℕ) :
    dominationPolynomial (book n) = hubsGF n := by
  symm
  unfold hubsGF dominationPolynomial
  calc
    _ = ∑ c : Selection n,
        if valid c then pairWeight c.1 * ∏ i, pairWeight (c.2 i) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (selectionEquiv n)
      intro c
      change (if valid c then pairWeight c.1 * ∏ i, pairWeight (c.2 i) else 0) =
        (if Dominates (book n) (toSet c) then (X : P)^(toSet c).card else 0)
      rw [set_weight]
      by_cases h : valid c
      · simp [h, (dominates_iff_valid c).mpr h]
      · have hn := not_congr (dominates_iff_valid c)
        simp [h, hn.mpr h]

#print axioms pairGF_eq
#print axioms nonemptyGF_eq
#print axioms noFirstGF_eq
#print axioms noLastGF_eq
#print axioms neitherGF_eq
#print axioms noHubsGF_eq
#print axioms hubsGF_factor
#print axioms dominationPolynomial_eq_hubsGF
end BookCompletion
