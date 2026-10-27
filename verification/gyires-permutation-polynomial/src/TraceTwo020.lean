module

public import TraceTwo020Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order020 (k : Fin 3) : Polynomial := traceTwo020Step35 k

theorem eval_t2Order020 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order020 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^20) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo020Step35 k) = _
  rw [eval_traceTwo020Step35]
  dsimp only [traceTwo020Real01, traceTwo020Real02, traceTwo020Real03, traceTwo020Real04, traceTwo020Real05, traceTwo020Real06, traceTwo020Real07, traceTwo020Real08, traceTwo020Real09, traceTwo020Real10, traceTwo020Real11, traceTwo020Real12, traceTwo020Real13, traceTwo020Real14, traceTwo020Real15, traceTwo020Real16, traceTwo020Real17, traceTwo020Real18, traceTwo020Real19, traceTwo020Real20, traceTwo020Real21, traceTwo020Real22, traceTwo020Real23, traceTwo020Real24, traceTwo020Real25, traceTwo020Real26, traceTwo020Real27, traceTwo020Real28, traceTwo020Real29, traceTwo020Real30, traceTwo020Real31, traceTwo020Real32, traceTwo020Real33, traceTwo020Real34, traceTwo020Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 14]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
