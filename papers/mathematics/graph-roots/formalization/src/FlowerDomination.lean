import FlowerGraph

noncomputable section
namespace SquareFlowerCompletion.Counting
attribute [local instance] Classical.propDecidable

def covered {n : ℕ} (c : Selection n) (x : Vertex n) : Prop :=
  selected c x ∨ ∃ y, selected c y ∧ (flower n).Adj x y

@[simp] theorem covered_hub {n : ℕ} (c : Selection n) :
    covered c none ↔ c.1=true ∨ ∃ i, (c.2 i).1=true ∨ (c.2 i).2.2=true := by
  simp [covered, exists_vertex, selected, directedEdge]

@[simp] theorem covered_first {n : ℕ} (c : Selection n) (i : Fin n) :
    covered c (some (i,0)) ↔ c.1=true ∨ (c.2 i).1=true ∨ (c.2 i).2.1=true := by
  simp [covered, exists_vertex, selected, directedEdge, or_comm, or_left_comm, or_assoc]

@[simp] theorem covered_middle {n : ℕ} (c : Selection n) (i : Fin n) :
    covered c (some (i,1)) ↔ (c.2 i).1=true ∨ (c.2 i).2.1=true ∨ (c.2 i).2.2=true := by
  simp [covered, exists_vertex, selected, directedEdge, exists_or,
    or_comm, or_left_comm, or_assoc]

@[simp] theorem covered_last {n : ℕ} (c : Selection n) (i : Fin n) :
    covered c (some (i,2)) ↔ c.1=true ∨ (c.2 i).2.1=true ∨ (c.2 i).2.2=true := by
  simp [covered, exists_vertex, selected, directedEdge, or_comm, or_left_comm, or_assoc]

def branchValid (root : Bool) (b : Branch) : Prop :=
  (root=true ∨ b.1=true ∨ b.2.1=true) ∧
  (b.1=true ∨ b.2.1=true ∨ b.2.2=true) ∧
  (root=true ∨ b.2.1=true ∨ b.2.2=true)

def valid {n : ℕ} (c : Selection n) : Prop :=
  (∀ i, branchValid c.1 (c.2 i)) ∧
    (c.1=true ∨ ∃ i, (c.2 i).1=true ∨ (c.2 i).2.2=true)

theorem branchValid_true (b : Branch) :
    branchValid true b ↔ b.1=true ∨ b.2.1=true ∨ b.2.2=true := by
  simp [branchValid]

theorem branchValid_false (b : Branch) :
    branchValid false b ↔ b.2.1=true ∨ (b.1=true ∧ b.2.2=true) := by
  simp only [branchValid, Bool.false_eq_true, false_or]
  tauto

theorem dominates_iff_valid {n : ℕ} (c : Selection n) :
    Dominates (flower n) (toSet c) ↔ valid c := by
  have hc : Dominates (flower n) (toSet c) ↔ ∀ x, covered c x := by
    simp [Dominates, covered]
  rw [hc]
  constructor
  · intro h
    refine ⟨?_, (covered_hub c).mp (h none)⟩
    intro i
    exact ⟨(covered_first c i).mp (h (some (i,0))),
      (covered_middle c i).mp (h (some (i,1))),
      (covered_last c i).mp (h (some (i,2)))⟩
  · rintro ⟨hlocal,hhub⟩ x
    cases x with
    | none => exact (covered_hub c).mpr hhub
    | some x =>
        rcases x with ⟨i,j⟩
        fin_cases j
        · exact (covered_first c i).mpr (hlocal i).1
        · exact (covered_middle c i).mpr (hlocal i).2.1
        · exact (covered_last c i).mpr (hlocal i).2.2

#print axioms covered_hub
#print axioms covered_first
#print axioms covered_middle
#print axioms covered_last
#print axioms dominates_iff_valid
end SquareFlowerCompletion.Counting
