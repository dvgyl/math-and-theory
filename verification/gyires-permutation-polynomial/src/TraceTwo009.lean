module

public import TraceTwo009Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def t2Order009 (k : Fin 3) : Polynomial := traceTwo009Step35 k

theorem eval_t2Order009 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order009 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^9) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo009Step35 k) = _
  rw [eval_traceTwo009Step35]
  dsimp only [traceTwo009Real01, traceTwo009Real02, traceTwo009Real03, traceTwo009Real04, traceTwo009Real05, traceTwo009Real06, traceTwo009Real07, traceTwo009Real08, traceTwo009Real09, traceTwo009Real10, traceTwo009Real11, traceTwo009Real12, traceTwo009Real13, traceTwo009Real14, traceTwo009Real15, traceTwo009Real16, traceTwo009Real17, traceTwo009Real18, traceTwo009Real19, traceTwo009Real20, traceTwo009Real21, traceTwo009Real22, traceTwo009Real23, traceTwo009Real24, traceTwo009Real25, traceTwo009Real26, traceTwo009Real27, traceTwo009Real28, traceTwo009Real29, traceTwo009Real30, traceTwo009Real31, traceTwo009Real32, traceTwo009Real33, traceTwo009Real34, traceTwo009Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 3]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
