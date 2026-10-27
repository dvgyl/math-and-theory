module

public import TraceTwo019Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order019 (k : Fin 3) : Polynomial := traceTwo019Step35 k

theorem eval_t2Order019 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order019 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^19) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo019Step35 k) = _
  rw [eval_traceTwo019Step35]
  dsimp only [traceTwo019Real01, traceTwo019Real02, traceTwo019Real03, traceTwo019Real04, traceTwo019Real05, traceTwo019Real06, traceTwo019Real07, traceTwo019Real08, traceTwo019Real09, traceTwo019Real10, traceTwo019Real11, traceTwo019Real12, traceTwo019Real13, traceTwo019Real14, traceTwo019Real15, traceTwo019Real16, traceTwo019Real17, traceTwo019Real18, traceTwo019Real19, traceTwo019Real20, traceTwo019Real21, traceTwo019Real22, traceTwo019Real23, traceTwo019Real24, traceTwo019Real25, traceTwo019Real26, traceTwo019Real27, traceTwo019Real28, traceTwo019Real29, traceTwo019Real30, traceTwo019Real31, traceTwo019Real32, traceTwo019Real33, traceTwo019Real34, traceTwo019Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 13]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
