import FlowerCounting

noncomputable section
open scoped BigOperators
open Polynomial
open SquareFlowerCompletion.Counting
namespace BookCompletion
attribute [local instance] Classical.propDecidable

abbrev Vertex (n : ℕ) := Bool ⊕ (Fin n × Bool)

def adjacency {n : ℕ} : Vertex n → Vertex n → Prop
  | .inl h, .inl k => h ≠ k
  | .inl h, .inr (_, j) => h = j
  | .inr (_, j), .inl h => j = h
  | .inr (i,j), .inr (k,t) => i = k ∧ j ≠ t

def book (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := adjacency
  symm := by
    intro x y h
    cases x <;> cases y <;> simpa [adjacency, eq_comm, ne_comm, and_comm] using h
  loopless := by
    intro x
    cases x <;> simp [adjacency]

@[simp] theorem book_adj (n : ℕ) (x y : Vertex n) :
    (book n).Adj x y ↔ adjacency x y := Iff.rfl

abbrev Branch := Bool × Bool
abbrev Selection (n : ℕ) := Branch × (Fin n → Branch)

def selected {n : ℕ} (c : Selection n) : Vertex n → Prop
  | .inl h => if h = false then c.1.1 = true else c.1.2 = true
  | .inr (i,j) => if j = false then (c.2 i).1 = true else (c.2 i).2 = true

def toSet {n : ℕ} (c : Selection n) : Finset (Vertex n) := Finset.univ.filter (selected c)
@[simp] theorem mem_toSet {n : ℕ} (c : Selection n) (x : Vertex n) :
    x ∈ toSet c ↔ selected c x := by simp [toSet]

def fromSet {n : ℕ} (s : Finset (Vertex n)) : Selection n :=
  ((decide (.inl false ∈ s), decide (.inl true ∈ s)), fun i =>
    (decide (.inr (i,false) ∈ s), decide (.inr (i,true) ∈ s)))

@[simp] theorem toSet_fromSet {n : ℕ} (s : Finset (Vertex n)) : toSet (fromSet s) = s := by
  ext x
  rcases x with h | ⟨i,j⟩
  · cases h <;> simp [selected, fromSet]
  · cases j <;> simp [selected, fromSet]

@[simp] theorem fromSet_toSet {n : ℕ} (c : Selection n) : fromSet (toSet c) = c := by
  rcases c with ⟨⟨u,v⟩,b⟩
  apply Prod.ext
  · cases u <;> cases v <;> simp [fromSet, selected]
  · funext i
    apply Prod.ext
    · cases h : (b i).1 <;> simp [fromSet, selected, h]
    · cases h : (b i).2 <;> simp [fromSet, selected, h]

def selectionEquiv (n : ℕ) : Selection n ≃ Finset (Vertex n) where
  toFun := toSet
  invFun := fromSet
  left_inv := fromSet_toSet
  right_inv := toSet_fromSet

def pairWeight (b : Branch) : P := bitWeight b.1 * bitWeight b.2

theorem set_weight {n : ℕ} (c : Selection n) :
    (X : P) ^ (toSet c).card = pairWeight c.1 * ∏ i, pairWeight (c.2 i) := by
  have h : (X : P) ^ (toSet c).card =
      ∏ x : Vertex n, if x ∈ toSet c then (X : P) else 1 := by
    rw [Fintype.prod_ite_mem]
    simp
  rw [h, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [mem_toSet, selected, Fintype.prod_bool, Bool.true_eq_false, ite_false, ite_true]
  simp only [pairWeight, bitWeight, mul_comm]

theorem exists_vertex {n : ℕ} (p : Vertex n → Prop) :
    (∃ x, p x) ↔ p (.inl false) ∨ p (.inl true) ∨
      ∃ i, p (.inr (i,false)) ∨ p (.inr (i,true)) := by
  constructor
  · rintro ⟨x,h⟩
    rcases x with j | ⟨i,j⟩
    · cases j
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · cases j
      · exact Or.inr (Or.inr ⟨i,Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨i,Or.inr h⟩)
  · rintro (h | h | ⟨i,h | h⟩)
    · exact ⟨.inl false,h⟩
    · exact ⟨.inl true,h⟩
    · exact ⟨.inr (i,false),h⟩
    · exact ⟨.inr (i,true),h⟩

#print axioms book
#print axioms toSet_fromSet
#print axioms fromSet_toSet
#print axioms set_weight
end BookCompletion
