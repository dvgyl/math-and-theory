import Resolution

namespace Kunisky
namespace Tree

variable {α : Type*} [DecidableEq α]

/-- The depth of every leaf occurrence labelled by `C`, counting repeated
occurrences separately. -/
def occurrenceDepths : Tree α → Clause α → List ℕ
  | .leaf D, C => if C = D then [0] else []
  | .node _ l r, C =>
      ((occurrenceDepths l C) ++ (occurrenceDepths r C)).map Nat.succ

/-- Recursive fair-branch mass is exactly the displayed dyadic sum over leaf
occurrences of `2⁻depth`, including repeated axiom clauses. -/
theorem mass_eq_occurrence_sum (t : Tree α) (C : Clause α) :
    t.mass C = ((t.occurrenceDepths C).map fun d => (1 / 2 : ℝ) ^ d).sum := by
  induction t with
  | leaf D =>
    by_cases h : C = D <;> simp [mass, occurrenceDepths, h]
  | node v l r hl hr =>
    simp only [mass, occurrenceDepths, List.map_map, Function.comp_def, pow_succ]
    rw [List.map_append, List.sum_append]
    simp only [List.sum_map_mul_right]
    rw [← hl, ← hr]
    ring

#print axioms mass_eq_occurrence_sum

end Tree
end Kunisky
