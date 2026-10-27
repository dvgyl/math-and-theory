module

public import TraceTwo015Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order015 (k : Fin 3) : Polynomial := traceTwo015Step35 k

theorem eval_t2Order015 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order015 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^15) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo015Step35 k) = _
  rw [eval_traceTwo015Step35]
  dsimp only [traceTwo015Real01, traceTwo015Real02, traceTwo015Real03, traceTwo015Real04, traceTwo015Real05, traceTwo015Real06, traceTwo015Real07, traceTwo015Real08, traceTwo015Real09, traceTwo015Real10, traceTwo015Real11, traceTwo015Real12, traceTwo015Real13, traceTwo015Real14, traceTwo015Real15, traceTwo015Real16, traceTwo015Real17, traceTwo015Real18, traceTwo015Real19, traceTwo015Real20, traceTwo015Real21, traceTwo015Real22, traceTwo015Real23, traceTwo015Real24, traceTwo015Real25, traceTwo015Real26, traceTwo015Real27, traceTwo015Real28, traceTwo015Real29, traceTwo015Real30, traceTwo015Real31, traceTwo015Real32, traceTwo015Real33, traceTwo015Real34, traceTwo015Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 9]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
