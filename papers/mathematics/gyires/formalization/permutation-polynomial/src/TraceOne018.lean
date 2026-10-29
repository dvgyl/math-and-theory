module

public import TraceOne018Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order018 (k : Fin 3) : Polynomial := traceOne018Step13 k

theorem eval_t1Order018 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order018 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^18) := by
  change SparsePolynomial.eval (evaluator z) (traceOne018Step13 k) = _
  rw [eval_traceOne018Step13]
  dsimp only [traceOne018Real01, traceOne018Real02, traceOne018Real03, traceOne018Real04, traceOne018Real05, traceOne018Real06, traceOne018Real07, traceOne018Real08, traceOne018Real09, traceOne018Real10, traceOne018Real11, traceOne018Real12, traceOne018Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 14]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
