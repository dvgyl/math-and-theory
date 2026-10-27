module

public import TraceOne012Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order012 (k : Fin 3) : Polynomial := traceOne012Step13 k

theorem eval_t1Order012 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order012 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^12) := by
  change SparsePolynomial.eval (evaluator z) (traceOne012Step13 k) = _
  rw [eval_traceOne012Step13]
  dsimp only [traceOne012Real01, traceOne012Real02, traceOne012Real03, traceOne012Real04, traceOne012Real05, traceOne012Real06, traceOne012Real07, traceOne012Real08, traceOne012Real09, traceOne012Real10, traceOne012Real11, traceOne012Real12, traceOne012Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 8]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
