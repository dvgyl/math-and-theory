import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-! Exact weighted enumeration of the branches in the leaf-mode counterexample. -/
noncomputable section
open scoped BigOperators
open Polynomial

namespace LeafMode.Counting

attribute [local instance] Classical.propDecidable

abbrev P := Polynomial ℤ
abbrev Branch (k : ℕ) := Bool × Bool × Finset (Fin k)

def bitWeight (b : Bool) : P := if b = true then X else 1

def bitCount (b : Bool) : ℕ := if b = true then 1 else 0

def branchWeight {k : ℕ} (c : Branch k) : P :=
  bitWeight c.1 * bitWeight c.2.1 * X ^ c.2.2.card

def branchSize {k : ℕ} (c : Branch k) : ℕ :=
  bitCount c.1 + bitCount c.2.1 + c.2.2.card

theorem bitWeight_eq (b : Bool) : bitWeight b = (X : P) ^ bitCount b := by
  cases b <;> simp [bitWeight, bitCount]

theorem branchWeight_eq {k : ℕ} (c : Branch k) :
    branchWeight c = (X : P) ^ branchSize c := by
  simp only [branchWeight, branchSize, bitWeight_eq, pow_add]

theorem rootWeight_eq {n k : ℕ} (root : Bool) (b : Fin n → Branch k) :
    bitWeight root * ∏ i, branchWeight (b i) =
      (X : P) ^ (bitCount root + ∑ i, branchSize (b i)) := by
  simp only [bitWeight_eq, branchWeight_eq, Finset.prod_pow_eq_pow_sum, pow_add]

theorem extendedWeight_eq {n k : ℕ} (root leaf : Bool) (b : Fin n → Branch k) :
    bitWeight root * bitWeight leaf * ∏ i, branchWeight (b i) =
      (X : P) ^ (bitCount root + bitCount leaf + ∑ i, branchSize (b i)) := by
  simp only [bitWeight_eq, branchWeight_eq, Finset.prod_pow_eq_pow_sum, pow_add]

def branchValid {k : ℕ} (root : Bool) (c : Branch k) : Prop :=
  (c.2.1 = true ∨ c.2.2 = Finset.univ) ∧
  (root = true ∨ c.1 = true ∨ c.2.1 = true)

def branchGF (k : ℕ) (root : Bool) : P :=
  ∑ c : Branch k, if branchValid root c then branchWeight c else 0

def branchNoU (k : ℕ) : P :=
  ∑ c : Branch k, if branchValid false c ∧ c.1 ≠ true then branchWeight c else 0

def rootValid {n k : ℕ} (root : Bool) (b : Fin n → Branch k) : Prop :=
  (∀ i, branchValid root (b i)) ∧ (root = true ∨ ∃ i, (b i).1 = true)

def extendedValid {n k : ℕ} (root leaf : Bool) (b : Fin n → Branch k) : Prop :=
  (∀ i, branchValid root (b i)) ∧
  (root = true ∨ (∃ i, (b i).1 = true) ∨ leaf = true) ∧
  (leaf = true ∨ root = true)

def rootGF (n k : ℕ) : P :=
  ∑ root : Bool, ∑ b : Fin n → Branch k,
    if rootValid root b then bitWeight root * ∏ i, branchWeight (b i) else 0

def extendedGF (n k : ℕ) : P :=
  ∑ root : Bool, ∑ leaf : Bool, ∑ b : Fin n → Branch k,
    if extendedValid root leaf b then
      bitWeight root * bitWeight leaf * ∏ i, branchWeight (b i) else 0

def S (k : ℕ) : P := (1 + X) * ((1 + X) ^ k + X ^ (k - 1))
def T (k : ℕ) : P := (1 + X) ^ (k + 1) + X ^ k

theorem leaf_sum (k : ℕ) :
    (∑ s : Finset (Fin k), (X : P) ^ s.card) = (1 + X) ^ k := by
  simpa using (Finset.prod_one_add (f := fun _ : Fin k => (X : P)) Finset.univ).symm

theorem branchValid_iff {k : ℕ} (hk : 0 < k) (root : Bool) (c : Branch k) :
    branchValid root c ↔
      (∀ j : Fin k, c.2.1 = true ∨ j ∈ c.2.2) ∧
      (c.2.1 = true ∨ c.1 = true ∨ c.2.2.Nonempty) ∧
      (root = true ∨ c.1 = true ∨ c.2.1 = true) := by
  classical
  rcases c with ⟨u, v, l⟩
  cases v <;> simp only [branchValid, Bool.false_eq_true, false_or, true_or,
    and_true, true_and, or_true, forall_true_iff, true_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨by simp, Or.inr ⟨⟨0, hk⟩, by simp⟩, h⟩
  · rintro ⟨hl, _, h⟩
    exact ⟨Finset.eq_univ_of_forall hl, h⟩

theorem branchGF_false (k : ℕ) :
    branchGF k false = (X : P) * ((1 + X) ^ (k + 1) + X ^ k) := by
  classical
  simp [branchGF, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight,
    ← Finset.mul_sum, leaf_sum]
  rw [pow_succ]
  ring

theorem branchGF_true (k : ℕ) :
    branchGF k true = (1 + (X : P)) * (X * (1 + X) ^ k + X ^ k) := by
  classical
  simp [branchGF, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight,
    ← Finset.mul_sum, leaf_sum]
  ring

theorem branchNoU_eq (k : ℕ) :
    branchNoU k = (X : P) * (1 + X) ^ k := by
  classical
  simp [branchNoU, Fintype.sum_prod_type, branchValid, branchWeight, bitWeight,
    ← Finset.mul_sum, leaf_sum]

theorem weighted_product_sum {α : Type*} [Fintype α] (n : ℕ)
    (pred : α → Prop) (w : α → P) :
    (∑ b : Fin n → α, if ∀ i, pred (b i) then ∏ i, w (b i) else 0) =
      (∑ a : α, if pred a then w a else 0) ^ n := by
  classical
  calc
    _ = ∑ b : Fin n → α, ∏ i, if pred (b i) then w (b i) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : ∀ i, pred (b i) <;> simp [Fintype.prod_ite_zero, h]
    _ = _ := (Fintype.sum_pow (fun a : α => if pred a then w a else 0) n).symm

theorem all_branch_sum (n k : ℕ) (root : Bool) :
    (∑ b : Fin n → Branch k,
      if ∀ i, branchValid root (b i) then ∏ i, branchWeight (b i) else 0) =
      branchGF k root ^ n :=
  weighted_product_sum n (branchValid root) branchWeight

theorem all_noU_sum (n k : ℕ) :
    (∑ b : Fin n → Branch k,
      if (∀ i, branchValid false (b i)) ∧ (¬ ∃ i, (b i).1 = true)
      then ∏ i, branchWeight (b i) else 0) = branchNoU k ^ n := by
  simpa [branchNoU, forall_and, not_exists] using
    weighted_product_sum n (fun c : Branch k => branchValid false c ∧ c.1 ≠ true)
      branchWeight

theorem rootGF_factor (n k : ℕ) :
    rootGF n k = (X : P) * branchGF k true ^ n +
      branchGF k false ^ n - branchNoU k ^ n := by
  classical
  have split (b : Fin n → Branch k) :
      (if (∀ i, branchValid false (b i)) ∧ (∃ i, (b i).1 = true)
        then ∏ i, branchWeight (b i) else 0) =
      (if ∀ i, branchValid false (b i) then ∏ i, branchWeight (b i) else 0) -
      (if (∀ i, branchValid false (b i)) ∧ (¬ ∃ i, (b i).1 = true)
        then ∏ i, branchWeight (b i) else 0) := by
    by_cases ha : ∀ i, branchValid false (b i) <;>
      by_cases hb : ∃ i, (b i).1 = true <;> simp [ha, hb]
  simp only [rootGF, Fintype.sum_bool, rootValid, bitWeight,
    Bool.false_eq_true, false_or, true_or, and_true, ite_true, ite_false, one_mul]
  simp_rw [split]
  rw [Finset.sum_sub_distrib, all_branch_sum, all_noU_sum]
  have true_sum :
      (∑ b : Fin n → Branch k,
        if ∀ i, branchValid true (b i) then X * ∏ i, branchWeight (b i) else 0) =
        (X : P) * branchGF k true ^ n := by
    rw [← all_branch_sum n k true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : ∀ i, branchValid true (b i) <;> simp [h]
  rw [true_sum]
  ring

theorem extendedGF_factor (n k : ℕ) :
    extendedGF n k = (X : P) * (1 + X) * branchGF k true ^ n +
      X * branchGF k false ^ n := by
  classical
  have mul_sum (root : Bool) (a : P) :
      (∑ b : Fin n → Branch k,
        if ∀ i, branchValid root (b i) then a * ∏ i, branchWeight (b i) else 0) =
        a * branchGF k root ^ n := by
    rw [← all_branch_sum n k root, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : ∀ i, branchValid root (b i) <;> simp [h]
  simp [extendedGF, Fintype.sum_bool, extendedValid, bitWeight, mul_sum]
  ring

theorem branchGF_true_eq {k : ℕ} (hk : 0 < k) :
    branchGF k true = (X : P) * S k := by
  rw [branchGF_true, S]
  have hx : (X : P) ^ k = X * X ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [hx]
  ring

theorem rootGF_eq {k : ℕ} (hk : 0 < k) (n : ℕ) :
    rootGF n k = (X : P) ^ n *
      (X * S k ^ n + T k ^ n - (1 + X) ^ (k * n)) := by
  rw [rootGF_factor, branchGF_true_eq hk, branchGF_false, branchNoU_eq]
  simp only [mul_pow, ← pow_mul, T]
  ring

theorem extendedGF_eq {k : ℕ} (hk : 0 < k) (n : ℕ) :
    extendedGF n k = (X : P) ^ (n + 1) *
      ((1 + X) * S k ^ n + T k ^ n) := by
  rw [extendedGF_factor, branchGF_true_eq hk, branchGF_false]
  simp only [mul_pow, T, pow_succ]
  ring

end LeafMode.Counting
