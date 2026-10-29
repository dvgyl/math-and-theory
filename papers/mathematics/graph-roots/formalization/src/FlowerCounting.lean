import FlowerDomination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
open Polynomial
namespace SquareFlowerCompletion.Counting
attribute [local instance] Classical.propDecidable

def branchGF (root : Bool) : P :=
  ∑ b : Branch, if branchValid root b then branchWeight b else 0

def branchNoEnd : P :=
  ∑ b : Branch,
    if branchValid false b ∧ b.1≠true ∧ b.2.2≠true then branchWeight b else 0

def rootGF (n : ℕ) : P :=
  ∑ root : Bool, ∑ b : Fin n → Branch,
    if valid (root,b) then bitWeight root * ∏ i, branchWeight (b i) else 0

theorem branchGF_true : branchGF true = (X : P)^3+3*X^2+3*X := by
  simp [branchGF, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight]
  ring

theorem branchGF_false : branchGF false = (X : P)^3+3*X^2+X := by
  simp [branchGF, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight]
  ring

theorem branchNoEnd_eq : branchNoEnd = (X : P) := by
  simp [branchNoEnd, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight]

theorem weighted_product_sum {α : Type*} [Fintype α] (n : ℕ)
    (pred : α → Prop) (w : α → P) :
    (∑ b : Fin n → α, if ∀ i, pred (b i) then ∏ i, w (b i) else 0) =
      (∑ a : α, if pred a then w a else 0)^n := by
  classical
  calc
    _ = ∑ b : Fin n → α, ∏ i, if pred (b i) then w (b i) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : ∀ i, pred (b i) <;> simp [Fintype.prod_ite_zero, h]
    _ = _ := (Fintype.sum_pow (fun a : α => if pred a then w a else 0) n).symm

theorem all_branch_sum (n : ℕ) (root : Bool) :
    (∑ b : Fin n → Branch,
      if ∀ i, branchValid root (b i) then ∏ i, branchWeight (b i) else 0) =
      branchGF root^n := weighted_product_sum n (branchValid root) branchWeight

theorem all_noEnd_sum (n : ℕ) :
    (∑ b : Fin n → Branch,
      if (∀ i, branchValid false (b i)) ∧ (¬ ∃ i, (b i).1=true ∨ (b i).2.2=true)
      then ∏ i, branchWeight (b i) else 0) = branchNoEnd^n := by
  simpa [branchNoEnd, forall_and, not_exists, not_or] using
    weighted_product_sum n
      (fun b : Branch => branchValid false b ∧ b.1≠true ∧ b.2.2≠true) branchWeight

theorem rootGF_factor (n : ℕ) :
    rootGF n = (X : P) * branchGF true^n + branchGF false^n - branchNoEnd^n := by
  have split (b : Fin n → Branch) :
      (if (∀ i, branchValid false (b i)) ∧ (∃ i, (b i).1=true ∨ (b i).2.2=true)
        then ∏ i, branchWeight (b i) else 0) =
      (if ∀ i, branchValid false (b i) then ∏ i, branchWeight (b i) else 0) -
      (if (∀ i, branchValid false (b i)) ∧ (¬ ∃ i, (b i).1=true ∨ (b i).2.2=true)
        then ∏ i, branchWeight (b i) else 0) := by
    by_cases ha : ∀ i, branchValid false (b i) <;>
      by_cases hb : ∃ i, (b i).1=true ∨ (b i).2.2=true <;> simp [ha,hb]
  simp only [rootGF, Fintype.sum_bool, valid, bitWeight,
    Bool.false_eq_true, false_or, true_or, and_true, ite_true, ite_false, one_mul]
  simp_rw [split]
  rw [Finset.sum_sub_distrib, all_branch_sum, all_noEnd_sum]
  have true_sum :
      (∑ b : Fin n → Branch,
        if ∀ i, branchValid true (b i) then X * ∏ i, branchWeight (b i) else 0) =
        (X : P) * branchGF true^n := by
    rw [← all_branch_sum n true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : ∀ i, branchValid true (b i) <;> simp [h]
  rw [true_sum]
  ring

theorem dominationPolynomial_eq_rootGF (n : ℕ) :
    dominationPolynomial (flower n) = rootGF n := by
  symm
  unfold rootGF dominationPolynomial
  calc
    _ = ∑ c : Selection n,
        if valid c then bitWeight c.1 * ∏ i, branchWeight (c.2 i) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (selectionEquiv n)
      intro c
      change (if valid c then bitWeight c.1 * ∏ i, branchWeight (c.2 i) else 0) =
        (if Dominates (flower n) (toSet c) then (X : P)^(toSet c).card else 0)
      rw [set_weight]
      by_cases h : valid c
      · simp [h, (dominates_iff_valid c).mpr h]
      · have hn := not_congr (dominates_iff_valid c)
        simp [h, hn.mpr h]

#print axioms branchGF_true
#print axioms branchGF_false
#print axioms branchNoEnd_eq
#print axioms weighted_product_sum
#print axioms rootGF_factor
#print axioms dominationPolynomial_eq_rootGF
end SquareFlowerCompletion.Counting
