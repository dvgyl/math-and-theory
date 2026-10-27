module

public import TraceOne011Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order011 (k : Fin 3) : Polynomial := traceOne011Step13 k

theorem eval_t1Order011 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order011 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^11) := by
  change SparsePolynomial.eval (evaluator z) (traceOne011Step13 k) = _
  rw [eval_traceOne011Step13]
  dsimp only [traceOne011Real01, traceOne011Real02, traceOne011Real03, traceOne011Real04, traceOne011Real05, traceOne011Real06, traceOne011Real07, traceOne011Real08, traceOne011Real09, traceOne011Real10, traceOne011Real11, traceOne011Real12, traceOne011Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 7]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
