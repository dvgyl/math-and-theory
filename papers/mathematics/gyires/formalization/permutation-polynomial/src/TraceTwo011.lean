module

public import TraceTwo011Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order011 (k : Fin 3) : Polynomial := traceTwo011Step35 k

theorem eval_t2Order011 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order011 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^11) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo011Step35 k) = _
  rw [eval_traceTwo011Step35]
  dsimp only [traceTwo011Real01, traceTwo011Real02, traceTwo011Real03, traceTwo011Real04, traceTwo011Real05, traceTwo011Real06, traceTwo011Real07, traceTwo011Real08, traceTwo011Real09, traceTwo011Real10, traceTwo011Real11, traceTwo011Real12, traceTwo011Real13, traceTwo011Real14, traceTwo011Real15, traceTwo011Real16, traceTwo011Real17, traceTwo011Real18, traceTwo011Real19, traceTwo011Real20, traceTwo011Real21, traceTwo011Real22, traceTwo011Real23, traceTwo011Real24, traceTwo011Real25, traceTwo011Real26, traceTwo011Real27, traceTwo011Real28, traceTwo011Real29, traceTwo011Real30, traceTwo011Real31, traceTwo011Real32, traceTwo011Real33, traceTwo011Real34, traceTwo011Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 5]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
