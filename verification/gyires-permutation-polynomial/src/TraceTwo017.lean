module

public import TraceTwo017Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order017 (k : Fin 3) : Polynomial := traceTwo017Step35 k

theorem eval_t2Order017 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order017 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^17) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo017Step35 k) = _
  rw [eval_traceTwo017Step35]
  dsimp only [traceTwo017Real01, traceTwo017Real02, traceTwo017Real03, traceTwo017Real04, traceTwo017Real05, traceTwo017Real06, traceTwo017Real07, traceTwo017Real08, traceTwo017Real09, traceTwo017Real10, traceTwo017Real11, traceTwo017Real12, traceTwo017Real13, traceTwo017Real14, traceTwo017Real15, traceTwo017Real16, traceTwo017Real17, traceTwo017Real18, traceTwo017Real19, traceTwo017Real20, traceTwo017Real21, traceTwo017Real22, traceTwo017Real23, traceTwo017Real24, traceTwo017Real25, traceTwo017Real26, traceTwo017Real27, traceTwo017Real28, traceTwo017Real29, traceTwo017Real30, traceTwo017Real31, traceTwo017Real32, traceTwo017Real33, traceTwo017Real34, traceTwo017Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 11]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
