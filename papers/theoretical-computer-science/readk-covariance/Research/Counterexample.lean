import Research.DecisionTree
import Mathlib.Tactic.FinCases

/-!
# A read-three counterexample to the variance refinement

The coordinates are x = 0, y = 1, z = 2, t = 3.  The root z chooses
between two representations of x AND y.  In each representation, t is
an irrelevant query immediately before the final relevant query.
-/

open scoped BigOperators

namespace ReadK
namespace Counterexample

def query (i : Fin 4) : Tree 4 := .node i (.leaf false) (.leaf true)

def left : Tree 4 := .node 0 (.leaf false) (.node 3 (query 1) (query 1))

def right : Tree 4 := .node 1 (.leaf false) (.node 3 (query 0) (query 0))

def witness : Tree 4 := .node 2 left right

theorem witness_regular : witness.Regular := by
  simp only [witness, left, right, query, Tree.Regular, Tree.count]
  decide

theorem witness_counts :
    witness.count 0 = 3 ∧ witness.count 1 = 3 ∧
    witness.count 2 = 1 ∧ witness.count 3 = 2 := by
  decide

theorem witness_read_three : ∀ i, witness.count i ≤ 3 := by
  intro i
  fin_cases i <;> decide

theorem witness_evaluates_and : witness.eval = fun a => a 0 && a 1 := by
  funext a
  cases hx : a 0 <;> cases hy : a 1 <;>
    simp [witness, left, right, query, Tree.eval, hx, hy]

theorem witness_mean : mean witness.eval = -(1 / 2 : ℝ) := by
  rw [witness_evaluates_and]
  norm_num [mean, avg_succ, restrict, val, Fin.cons_zero, Fin.cons_succ]

theorem witness_variance : cov witness.eval witness.eval = (3 / 4 : ℝ) := by
  rw [witness_evaluates_and]
  norm_num [cov, mean, avg_succ, restrict, val, Fin.cons_zero, Fin.cons_succ]

theorem witness_covariance : witness.covariance = (5 / 4 : ℝ) := by
  norm_num [witness, left, right, query, Tree.covariance, Tree.eval,
    cov, mean, avg_succ, restrict, val, Fin.cons_zero, Fin.cons_succ]

theorem logCount_three_lt : logCount 3 < (5 / 3 : ℝ) := by
  have hlog : Real.log ((3 : ℝ) ^ 3) < Real.log ((2 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  simp only [Real.log_pow] at hlog
  norm_num at hlog
  rw [logCount_of_pos (by decide : 0 < 3)]
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  linarith

/-- The proposed `log₂(k) * Var(f)` bound fails for a regular read-three tree. -/
theorem violates_variance_bound :
    logCount 3 * cov witness.eval witness.eval < witness.covariance := by
  rw [witness_variance, witness_covariance]
  have h := logCount_three_lt
  nlinarith

/-- A fully quantified existential refutation of the variance refinement. -/
theorem variance_refinement_false :
    ∃ t : Tree 4, t.Regular ∧ (∀ i, t.count i ≤ 3) ∧
      logCount 3 * cov t.eval t.eval < t.covariance :=
  ⟨witness, witness_regular, witness_read_three, violates_variance_bound⟩

end Counterexample
end ReadK
