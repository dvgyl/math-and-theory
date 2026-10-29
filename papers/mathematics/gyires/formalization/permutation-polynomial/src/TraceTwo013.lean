module

public import TraceTwo013Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order013 (k : Fin 3) : Polynomial := traceTwo013Step35 k

theorem eval_t2Order013 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order013 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^13) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo013Step35 k) = _
  rw [eval_traceTwo013Step35]
  dsimp only [traceTwo013Real01, traceTwo013Real02, traceTwo013Real03, traceTwo013Real04, traceTwo013Real05, traceTwo013Real06, traceTwo013Real07, traceTwo013Real08, traceTwo013Real09, traceTwo013Real10, traceTwo013Real11, traceTwo013Real12, traceTwo013Real13, traceTwo013Real14, traceTwo013Real15, traceTwo013Real16, traceTwo013Real17, traceTwo013Real18, traceTwo013Real19, traceTwo013Real20, traceTwo013Real21, traceTwo013Real22, traceTwo013Real23, traceTwo013Real24, traceTwo013Real25, traceTwo013Real26, traceTwo013Real27, traceTwo013Real28, traceTwo013Real29, traceTwo013Real30, traceTwo013Real31, traceTwo013Real32, traceTwo013Real33, traceTwo013Real34, traceTwo013Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 7]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
