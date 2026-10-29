import Completion
import Concentration
import SourceMass

namespace Kunisky

/-- The concrete policy on all consistent proper clauses and the distinguished
all-positive clause.  Every field is proved by the explicit resolution rules. -/
noncomputable def fullPolicy (n : ℕ) (hn : 3 ≤ n) :
    ResolutionPolicy (fullFormula n) (PolicyState n) where
  target := PolicyState.target n
  left := PolicyState.left hn
  right := PolicyState.right hn
  label := PolicyState.clause
  pivot := PolicyState.pivot hn
  complete := PolicyState.complete
  target_mem := PolicyState.target_mem n
  complete_valid := PolicyState.complete_valid
  complete_conclusion := PolicyState.complete_conclusion
  left_pivot := PolicyState.left_pivot hn
  right_pivot := PolicyState.right_pivot hn
  resolve := PolicyState.resolves hn

/-- For every number of variables at least three and every positive tolerance,
there is an actual finite resolution refutation of the complete full-clause
formula whose all-positive axiom has fair-branch mass greater than `1 - ε`. -/
theorem exists_concentrated_refutation (n : ℕ) (hn : 3 ≤ n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Tree (Fin n), t.Valid (fullFormula n) ∧ t.conclusion = ∅ ∧
      1 - ε < t.mass (positiveClause n) := by
  have h := (fullPolicy n hn).exists_concentrated_tree PolicyState.rank
    PolicyState.rank_zero (PolicyState.rank_left hn) n PolicyState.rank_bound
    (PolicyState.initial n) ε hε
  simpa only [fullPolicy, PolicyState.clause_initial, PolicyState.clause_target] using h

#print axioms exists_concentrated_refutation

end Kunisky
