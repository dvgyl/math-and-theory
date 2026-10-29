module

public import TraceOne016Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order016 (k : Fin 3) : Polynomial := traceOne016Step13 k

theorem eval_t1Order016 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order016 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^16) := by
  change SparsePolynomial.eval (evaluator z) (traceOne016Step13 k) = _
  rw [eval_traceOne016Step13]
  dsimp only [traceOne016Real01, traceOne016Real02, traceOne016Real03, traceOne016Real04, traceOne016Real05, traceOne016Real06, traceOne016Real07, traceOne016Real08, traceOne016Real09, traceOne016Real10, traceOne016Real11, traceOne016Real12, traceOne016Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 12]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
