module

public import TraceTwo008Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def t2Order008 (k : Fin 3) : Polynomial := traceTwo008Step35 k

theorem eval_t2Order008 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order008 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^8) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo008Step35 k) = _
  rw [eval_traceTwo008Step35]
  dsimp only [traceTwo008Real01, traceTwo008Real02, traceTwo008Real03, traceTwo008Real04, traceTwo008Real05, traceTwo008Real06, traceTwo008Real07, traceTwo008Real08, traceTwo008Real09, traceTwo008Real10, traceTwo008Real11, traceTwo008Real12, traceTwo008Real13, traceTwo008Real14, traceTwo008Real15, traceTwo008Real16, traceTwo008Real17, traceTwo008Real18, traceTwo008Real19, traceTwo008Real20, traceTwo008Real21, traceTwo008Real22, traceTwo008Real23, traceTwo008Real24, traceTwo008Real25, traceTwo008Real26, traceTwo008Real27, traceTwo008Real28, traceTwo008Real29, traceTwo008Real30, traceTwo008Real31, traceTwo008Real32, traceTwo008Real33, traceTwo008Real34, traceTwo008Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 2]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
