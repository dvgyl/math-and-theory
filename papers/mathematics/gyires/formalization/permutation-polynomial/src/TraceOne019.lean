module

public import TraceOne019Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order019 (k : Fin 3) : Polynomial := traceOne019Step13 k

theorem eval_t1Order019 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order019 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^19) := by
  change SparsePolynomial.eval (evaluator z) (traceOne019Step13 k) = _
  rw [eval_traceOne019Step13]
  dsimp only [traceOne019Real01, traceOne019Real02, traceOne019Real03, traceOne019Real04, traceOne019Real05, traceOne019Real06, traceOne019Real07, traceOne019Real08, traceOne019Real09, traceOne019Real10, traceOne019Real11, traceOne019Real12, traceOne019Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 15]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
