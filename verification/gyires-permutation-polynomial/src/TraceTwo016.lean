module

public import TraceTwo016Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order016 (k : Fin 3) : Polynomial := traceTwo016Step35 k

theorem eval_t2Order016 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order016 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^16) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo016Step35 k) = _
  rw [eval_traceTwo016Step35]
  dsimp only [traceTwo016Real01, traceTwo016Real02, traceTwo016Real03, traceTwo016Real04, traceTwo016Real05, traceTwo016Real06, traceTwo016Real07, traceTwo016Real08, traceTwo016Real09, traceTwo016Real10, traceTwo016Real11, traceTwo016Real12, traceTwo016Real13, traceTwo016Real14, traceTwo016Real15, traceTwo016Real16, traceTwo016Real17, traceTwo016Real18, traceTwo016Real19, traceTwo016Real20, traceTwo016Real21, traceTwo016Real22, traceTwo016Real23, traceTwo016Real24, traceTwo016Real25, traceTwo016Real26, traceTwo016Real27, traceTwo016Real28, traceTwo016Real29, traceTwo016Real30, traceTwo016Real31, traceTwo016Real32, traceTwo016Real33, traceTwo016Real34, traceTwo016Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 10]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
