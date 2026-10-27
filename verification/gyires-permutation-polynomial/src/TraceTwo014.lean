module

public import TraceTwo014Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order014 (k : Fin 3) : Polynomial := traceTwo014Step35 k

theorem eval_t2Order014 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order014 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^14) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo014Step35 k) = _
  rw [eval_traceTwo014Step35]
  dsimp only [traceTwo014Real01, traceTwo014Real02, traceTwo014Real03, traceTwo014Real04, traceTwo014Real05, traceTwo014Real06, traceTwo014Real07, traceTwo014Real08, traceTwo014Real09, traceTwo014Real10, traceTwo014Real11, traceTwo014Real12, traceTwo014Real13, traceTwo014Real14, traceTwo014Real15, traceTwo014Real16, traceTwo014Real17, traceTwo014Real18, traceTwo014Real19, traceTwo014Real20, traceTwo014Real21, traceTwo014Real22, traceTwo014Real23, traceTwo014Real24, traceTwo014Real25, traceTwo014Real26, traceTwo014Real27, traceTwo014Real28, traceTwo014Real29, traceTwo014Real30, traceTwo014Real31, traceTwo014Real32, traceTwo014Real33, traceTwo014Real34, traceTwo014Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 8]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
