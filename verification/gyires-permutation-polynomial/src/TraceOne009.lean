module

public import TraceOne009Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def t1Order009 (k : Fin 3) : Polynomial := traceOne009Step13 k

theorem eval_t1Order009 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order009 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^9) := by
  change SparsePolynomial.eval (evaluator z) (traceOne009Step13 k) = _
  rw [eval_traceOne009Step13]
  dsimp only [traceOne009Real01, traceOne009Real02, traceOne009Real03, traceOne009Real04, traceOne009Real05, traceOne009Real06, traceOne009Real07, traceOne009Real08, traceOne009Real09, traceOne009Real10, traceOne009Real11, traceOne009Real12, traceOne009Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 5]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
