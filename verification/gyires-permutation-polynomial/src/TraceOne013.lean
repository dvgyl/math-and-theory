module

public import TraceOne013Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order013 (k : Fin 3) : Polynomial := traceOne013Step13 k

theorem eval_t1Order013 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order013 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^13) := by
  change SparsePolynomial.eval (evaluator z) (traceOne013Step13 k) = _
  rw [eval_traceOne013Step13]
  dsimp only [traceOne013Real01, traceOne013Real02, traceOne013Real03, traceOne013Real04, traceOne013Real05, traceOne013Real06, traceOne013Real07, traceOne013Real08, traceOne013Real09, traceOne013Real10, traceOne013Real11, traceOne013Real12, traceOne013Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 9]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
