module

public import TraceOne010Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def t1Order010 (k : Fin 3) : Polynomial := traceOne010Step13 k

theorem eval_t1Order010 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order010 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^10) := by
  change SparsePolynomial.eval (evaluator z) (traceOne010Step13 k) = _
  rw [eval_traceOne010Step13]
  dsimp only [traceOne010Real01, traceOne010Real02, traceOne010Real03, traceOne010Real04, traceOne010Real05, traceOne010Real06, traceOne010Real07, traceOne010Real08, traceOne010Real09, traceOne010Real10, traceOne010Real11, traceOne010Real12, traceOne010Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 6]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
