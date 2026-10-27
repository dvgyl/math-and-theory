module

public import PackedPolynomialData
public import TraceOne021Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order021 (k : Fin 3) : Polynomial := traceOne021Step13 k

theorem eval_t1Order021 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order021 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^21) := by
  change SparsePolynomial.eval (evaluator z) (traceOne021Step13 k) = _
  rw [eval_traceOne021Step13]
  dsimp only [traceOne021Real01, traceOne021Real02, traceOne021Real03, traceOne021Real04, traceOne021Real05, traceOne021Real06, traceOne021Real07, traceOne021Real08, traceOne021Real09, traceOne021Real10, traceOne021Real11, traceOne021Real12, traceOne021Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 17]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
