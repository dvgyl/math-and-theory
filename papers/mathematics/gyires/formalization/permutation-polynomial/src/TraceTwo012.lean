module

public import TraceTwo012Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order012 (k : Fin 3) : Polynomial := traceTwo012Step35 k

theorem eval_t2Order012 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order012 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^12) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo012Step35 k) = _
  rw [eval_traceTwo012Step35]
  dsimp only [traceTwo012Real01, traceTwo012Real02, traceTwo012Real03, traceTwo012Real04, traceTwo012Real05, traceTwo012Real06, traceTwo012Real07, traceTwo012Real08, traceTwo012Real09, traceTwo012Real10, traceTwo012Real11, traceTwo012Real12, traceTwo012Real13, traceTwo012Real14, traceTwo012Real15, traceTwo012Real16, traceTwo012Real17, traceTwo012Real18, traceTwo012Real19, traceTwo012Real20, traceTwo012Real21, traceTwo012Real22, traceTwo012Real23, traceTwo012Real24, traceTwo012Real25, traceTwo012Real26, traceTwo012Real27, traceTwo012Real28, traceTwo012Real29, traceTwo012Real30, traceTwo012Real31, traceTwo012Real32, traceTwo012Real33, traceTwo012Real34, traceTwo012Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 6]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
