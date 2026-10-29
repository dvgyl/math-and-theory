module

public import TraceOne017Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order017 (k : Fin 3) : Polynomial := traceOne017Step13 k

theorem eval_t1Order017 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order017 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^17) := by
  change SparsePolynomial.eval (evaluator z) (traceOne017Step13 k) = _
  rw [eval_traceOne017Step13]
  dsimp only [traceOne017Real01, traceOne017Real02, traceOne017Real03, traceOne017Real04, traceOne017Real05, traceOne017Real06, traceOne017Real07, traceOne017Real08, traceOne017Real09, traceOne017Real10, traceOne017Real11, traceOne017Real12, traceOne017Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 13]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
