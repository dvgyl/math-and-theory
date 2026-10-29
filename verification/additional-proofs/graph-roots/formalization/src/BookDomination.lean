import BookGraph

noncomputable section
open SquareFlowerCompletion.Counting
namespace BookCompletion
attribute [local instance] Classical.propDecidable

def covered {n : ℕ} (c : Selection n) (x : Vertex n) : Prop :=
  selected c x ∨ ∃ y, selected c y ∧ (book n).Adj x y

@[simp] theorem covered_leftHub {n : ℕ} (c : Selection n) :
    covered c (.inl false) ↔ c.1.1=true ∨ c.1.2=true ∨ ∃ i, (c.2 i).1=true := by
  simp [covered, exists_vertex, selected, adjacency, exists_or]

@[simp] theorem covered_rightHub {n : ℕ} (c : Selection n) :
    covered c (.inl true) ↔ c.1.1=true ∨ c.1.2=true ∨ ∃ i, (c.2 i).2=true := by
  simp [covered, exists_vertex, selected, adjacency, exists_or, or_comm, or_left_comm, or_assoc]

@[simp] theorem covered_first {n : ℕ} (c : Selection n) (i : Fin n) :
    covered c (.inr (i,false)) ↔ c.1.1=true ∨ (c.2 i).1=true ∨ (c.2 i).2=true := by
  simp [covered, exists_vertex, selected, adjacency, exists_or, or_comm, or_left_comm, or_assoc]

@[simp] theorem covered_last {n : ℕ} (c : Selection n) (i : Fin n) :
    covered c (.inr (i,true)) ↔ c.1.2=true ∨ (c.2 i).1=true ∨ (c.2 i).2=true := by
  simp [covered, exists_vertex, selected, adjacency, exists_or, or_comm, or_left_comm, or_assoc]

def pairNonempty (b : Branch) : Prop := b.1=true ∨ b.2=true

def branchValid (h b : Branch) : Prop :=
  (h.1=true ∨ pairNonempty b) ∧ (h.2=true ∨ pairNonempty b)

def valid {n : ℕ} (c : Selection n) : Prop :=
  (∀ i, branchValid c.1 (c.2 i)) ∧
  (c.1.1=true ∨ c.1.2=true ∨ ∃ i, (c.2 i).1=true) ∧
  (c.1.1=true ∨ c.1.2=true ∨ ∃ i, (c.2 i).2=true)

theorem dominates_iff_valid {n : ℕ} (c : Selection n) :
    Dominates (book n) (toSet c) ↔ valid c := by
  have hc : Dominates (book n) (toSet c) ↔ ∀ x, covered c x := by
    simp [Dominates, covered]
  rw [hc]
  constructor
  · intro h
    refine ⟨?_, (covered_leftHub c).mp (h (.inl false)),
      (covered_rightHub c).mp (h (.inl true))⟩
    intro i
    exact ⟨(covered_first c i).mp (h (.inr (i,false))),
      (covered_last c i).mp (h (.inr (i,true)))⟩
  · rintro ⟨hlocal,hu,hv⟩ x
    rcases x with h | ⟨i,j⟩
    · cases h
      · exact (covered_leftHub c).mpr hu
      · exact (covered_rightHub c).mpr hv
    · cases j
      · exact (covered_first c i).mpr (hlocal i).1
      · exact (covered_last c i).mpr (hlocal i).2

#print axioms covered_leftHub
#print axioms covered_rightHub
#print axioms covered_first
#print axioms covered_last
#print axioms dominates_iff_valid
end BookCompletion
