module

public import TraceTwo010Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def t2Order010 (k : Fin 3) : Polynomial := traceTwo010Step35 k

theorem eval_t2Order010 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order010 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^10) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo010Step35 k) = _
  rw [eval_traceTwo010Step35]
  dsimp only [traceTwo010Real01, traceTwo010Real02, traceTwo010Real03, traceTwo010Real04, traceTwo010Real05, traceTwo010Real06, traceTwo010Real07, traceTwo010Real08, traceTwo010Real09, traceTwo010Real10, traceTwo010Real11, traceTwo010Real12, traceTwo010Real13, traceTwo010Real14, traceTwo010Real15, traceTwo010Real16, traceTwo010Real17, traceTwo010Real18, traceTwo010Real19, traceTwo010Real20, traceTwo010Real21, traceTwo010Real22, traceTwo010Real23, traceTwo010Real24, traceTwo010Real25, traceTwo010Real26, traceTwo010Real27, traceTwo010Real28, traceTwo010Real29, traceTwo010Real30, traceTwo010Real31, traceTwo010Real32, traceTwo010Real33, traceTwo010Real34, traceTwo010Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 4]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
