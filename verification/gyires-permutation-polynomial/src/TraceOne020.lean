module

public import TraceOne020Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order020 (k : Fin 3) : Polynomial := traceOne020Step13 k

theorem eval_t1Order020 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order020 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^20) := by
  change SparsePolynomial.eval (evaluator z) (traceOne020Step13 k) = _
  rw [eval_traceOne020Step13]
  dsimp only [traceOne020Real01, traceOne020Real02, traceOne020Real03, traceOne020Real04, traceOne020Real05, traceOne020Real06, traceOne020Real07, traceOne020Real08, traceOne020Real09, traceOne020Real10, traceOne020Real11, traceOne020Real12, traceOne020Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 16]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
