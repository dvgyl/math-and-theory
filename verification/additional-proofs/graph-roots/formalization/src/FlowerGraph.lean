import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

noncomputable section
open scoped BigOperators
open Polynomial
namespace SquareFlowerCompletion.Counting
attribute [local instance] Classical.propDecidable

abbrev Vertex (n : ℕ) := Option (Fin n × Fin 3)

def directedEdge {n : ℕ} : Vertex n → Vertex n → Prop
  | none, some (_, j) => j = 0 ∨ j = 2
  | some (i, j), some (k, t) => i = k ∧ ((j = 0 ∧ t = 1) ∨ (j = 1 ∧ t = 2))
  | _, _ => False

def flower (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := directedEdge x y ∨ directedEdge y x
  symm := by intro x y h; exact h.symm
  loopless := by
    intro x
    cases x with
    | none => simp [directedEdge]
    | some x => rcases x with ⟨i,j⟩; fin_cases j <;> simp [directedEdge]

@[simp] theorem flower_adj (n : ℕ) (x y : Vertex n) :
    (flower n).Adj x y ↔ directedEdge x y ∨ directedEdge y x := Iff.rfl

def Dominates {α : Type*} [DecidableEq α] (G : SimpleGraph α) (s : Finset α) : Prop :=
  ∀ x, x ∈ s ∨ ∃ y, y ∈ s ∧ G.Adj x y

def dominationPolynomial {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Polynomial ℤ :=
  ∑ s : Finset α, if Dominates G s then X ^ s.card else 0

theorem coeff_dominationPolynomial {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (d : ℕ) :
    (dominationPolynomial G).coeff d =
      ((Finset.univ.filter (fun s : Finset α => Dominates G s ∧ s.card = d)).card : ℤ) := by
  classical
  simp only [dominationPolynomial, finset_sum_coeff]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : Dominates G s
  · simp [h, coeff_X_pow, eq_comm]
  · simp [h]

abbrev Branch := Bool × Bool × Bool
abbrev Selection (n : ℕ) := Bool × (Fin n → Branch)
abbrev P := Polynomial ℤ

def selected {n : ℕ} (c : Selection n) : Vertex n → Prop
  | none => c.1 = true
  | some (i,j) => if j=0 then (c.2 i).1 = true
      else if j=1 then (c.2 i).2.1 = true else (c.2 i).2.2 = true

def toSet {n : ℕ} (c : Selection n) : Finset (Vertex n) := Finset.univ.filter (selected c)
@[simp] theorem mem_toSet {n : ℕ} (c : Selection n) (x : Vertex n) :
    x ∈ toSet c ↔ selected c x := by simp [toSet]

def fromSet {n : ℕ} (s : Finset (Vertex n)) : Selection n :=
  (decide (none ∈ s), fun i =>
    (decide (some (i,0) ∈ s), decide (some (i,1) ∈ s), decide (some (i,2) ∈ s)))

@[simp] theorem toSet_fromSet {n : ℕ} (s : Finset (Vertex n)) : toSet (fromSet s) = s := by
  ext x
  cases x with
  | none => simp [selected, fromSet]
  | some x => rcases x with ⟨i,j⟩; fin_cases j <;> simp [selected, fromSet]

@[simp] theorem fromSet_toSet {n : ℕ} (c : Selection n) : fromSet (toSet c) = c := by
  rcases c with ⟨r,b⟩
  apply Prod.ext
  · cases r <;> simp [fromSet, selected]
  · funext i
    apply Prod.ext
    · cases h : (b i).1 <;> simp [fromSet, selected, h]
    · apply Prod.ext
      · cases h : (b i).2.1 <;> simp [fromSet, selected, h]
      · cases h : (b i).2.2 <;> simp [fromSet, selected, h]

def selectionEquiv (n : ℕ) : Selection n ≃ Finset (Vertex n) where
  toFun := toSet
  invFun := fromSet
  left_inv := fromSet_toSet
  right_inv := toSet_fromSet

def bitWeight (b : Bool) : P := if b=true then X else 1
def branchWeight (b : Branch) : P := bitWeight b.1 * bitWeight b.2.1 * bitWeight b.2.2

theorem set_weight {n : ℕ} (c : Selection n) :
    (X : P) ^ (toSet c).card = bitWeight c.1 * ∏ i, branchWeight (c.2 i) := by
  have h : (X : P) ^ (toSet c).card =
      ∏ x : Vertex n, if x ∈ toSet c then (X : P) else 1 := by
    rw [Fintype.prod_ite_mem]
    simp
  rw [h, Fintype.prod_option, Fintype.prod_prod_type]
  simp [Fin.prod_univ_three, selected, bitWeight, branchWeight]

theorem exists_vertex {n : ℕ} (p : Vertex n → Prop) :
    (∃ x, p x) ↔ p none ∨ ∃ i, p (some (i,0)) ∨ p (some (i,1)) ∨ p (some (i,2)) := by
  constructor
  · rintro ⟨x,h⟩
    cases x with
    | none => exact Or.inl h
    | some x =>
        rcases x with ⟨i,j⟩
        fin_cases j
        · exact Or.inr ⟨i, Or.inl h⟩
        · exact Or.inr ⟨i, Or.inr (Or.inl h)⟩
        · exact Or.inr ⟨i, Or.inr (Or.inr h)⟩
  · rintro (h | ⟨i, h | h | h⟩)
    · exact ⟨none,h⟩
    · exact ⟨some (i,0),h⟩
    · exact ⟨some (i,1),h⟩
    · exact ⟨some (i,2),h⟩

#print axioms coeff_dominationPolynomial
#print axioms toSet_fromSet
#print axioms fromSet_toSet
#print axioms set_weight
end SquareFlowerCompletion.Counting
