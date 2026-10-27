module

public import TraceOne014Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order014 (k : Fin 3) : Polynomial := traceOne014Step13 k

theorem eval_t1Order014 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order014 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^14) := by
  change SparsePolynomial.eval (evaluator z) (traceOne014Step13 k) = _
  rw [eval_traceOne014Step13]
  dsimp only [traceOne014Real01, traceOne014Real02, traceOne014Real03, traceOne014Real04, traceOne014Real05, traceOne014Real06, traceOne014Real07, traceOne014Real08, traceOne014Real09, traceOne014Real10, traceOne014Real11, traceOne014Real12, traceOne014Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 10]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
