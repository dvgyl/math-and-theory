module

public import TraceOne015Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order015 (k : Fin 3) : Polynomial := traceOne015Step13 k

theorem eval_t1Order015 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order015 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^15) := by
  change SparsePolynomial.eval (evaluator z) (traceOne015Step13 k) = _
  rw [eval_traceOne015Step13]
  dsimp only [traceOne015Real01, traceOne015Real02, traceOne015Real03, traceOne015Real04, traceOne015Real05, traceOne015Real06, traceOne015Real07, traceOne015Real08, traceOne015Real09, traceOne015Real10, traceOne015Real11, traceOne015Real12, traceOne015Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 11]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
