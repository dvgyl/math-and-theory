module

public import PackedPolynomialData
public import TraceTwo022Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order022 (k : Fin 3) : Polynomial := traceTwo022Step35 k

theorem eval_t2Order022 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order022 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^22) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo022Step35 k) = _
  rw [eval_traceTwo022Step35]
  dsimp only [traceTwo022Real01, traceTwo022Real02, traceTwo022Real03, traceTwo022Real04, traceTwo022Real05, traceTwo022Real06, traceTwo022Real07, traceTwo022Real08, traceTwo022Real09, traceTwo022Real10, traceTwo022Real11, traceTwo022Real12, traceTwo022Real13, traceTwo022Real14, traceTwo022Real15, traceTwo022Real16, traceTwo022Real17, traceTwo022Real18, traceTwo022Real19, traceTwo022Real20, traceTwo022Real21, traceTwo022Real22, traceTwo022Real23, traceTwo022Real24, traceTwo022Real25, traceTwo022Real26, traceTwo022Real27, traceTwo022Real28, traceTwo022Real29, traceTwo022Real30, traceTwo022Real31, traceTwo022Real32, traceTwo022Real33, traceTwo022Real34, traceTwo022Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 16]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
