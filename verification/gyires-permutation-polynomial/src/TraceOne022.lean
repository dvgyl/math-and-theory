module

public import PackedPolynomialData
public import TraceOne022Steps03

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t1Order022 (k : Fin 3) : Polynomial := traceOne022Step13 k

theorem eval_t1Order022 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t1Order022 k) =
      Matrix.trace (PermutationTransfer.transferOne ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^22) := by
  change SparsePolynomial.eval (evaluator z) (traceOne022Step13 k) = _
  rw [eval_traceOne022Step13]
  dsimp only [traceOne022Real01, traceOne022Real02, traceOne022Real03, traceOne022Real04, traceOne022Real05, traceOne022Real06, traceOne022Real07, traceOne022Real08, traceOne022Real09, traceOne022Real10, traceOne022Real11, traceOne022Real12, traceOne022Real13]
  rw [one_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 18]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
