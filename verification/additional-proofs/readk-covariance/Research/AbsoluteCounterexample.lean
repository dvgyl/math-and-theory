import Research.Absolute
import Research.Counterexample

/-! The four-variable witness has no cancellation between node covariances. -/

namespace ReadK.Counterexample

theorem witness_absoluteCovariance :
    witness.absoluteCovariance = (5 / 4 : ℝ) := by
  norm_num [witness, left, right, query, Tree.absoluteCovariance, Tree.eval,
    cov, mean, avg_succ, restrict, val, Fin.cons_zero, Fin.cons_succ]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  norm_num

end ReadK.Counterexample
