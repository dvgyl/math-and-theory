module

public import TraceTwo018Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order018 (k : Fin 3) : Polynomial := traceTwo018Step35 k

theorem eval_t2Order018 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order018 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^18) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo018Step35 k) = _
  rw [eval_traceTwo018Step35]
  dsimp only [traceTwo018Real01, traceTwo018Real02, traceTwo018Real03, traceTwo018Real04, traceTwo018Real05, traceTwo018Real06, traceTwo018Real07, traceTwo018Real08, traceTwo018Real09, traceTwo018Real10, traceTwo018Real11, traceTwo018Real12, traceTwo018Real13, traceTwo018Real14, traceTwo018Real15, traceTwo018Real16, traceTwo018Real17, traceTwo018Real18, traceTwo018Real19, traceTwo018Real20, traceTwo018Real21, traceTwo018Real22, traceTwo018Real23, traceTwo018Real24, traceTwo018Real25, traceTwo018Real26, traceTwo018Real27, traceTwo018Real28, traceTwo018Real29, traceTwo018Real30, traceTwo018Real31, traceTwo018Real32, traceTwo018Real33, traceTwo018Real34, traceTwo018Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 12]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
