module

public import PackedPolynomialData
public import TraceTwo021Steps08

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def t2Order021 (k : Fin 3) : Polynomial := traceTwo021Step35 k

theorem eval_t2Order021 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (t2Order021 k) =
      Matrix.trace (PermutationTransfer.transferTwo ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k)^21) := by
  change SparsePolynomial.eval (evaluator z) (traceTwo021Step35 k) = _
  rw [eval_traceTwo021Step35]
  dsimp only [traceTwo021Real01, traceTwo021Real02, traceTwo021Real03, traceTwo021Real04, traceTwo021Real05, traceTwo021Real06, traceTwo021Real07, traceTwo021Real08, traceTwo021Real09, traceTwo021Real10, traceTwo021Real11, traceTwo021Real12, traceTwo021Real13, traceTwo021Real14, traceTwo021Real15, traceTwo021Real16, traceTwo021Real17, traceTwo021Real18, traceTwo021Real19, traceTwo021Real20, traceTwo021Real21, traceTwo021Real22, traceTwo021Real23, traceTwo021Real24, traceTwo021Real25, traceTwo021Real26, traceTwo021Real27, traceTwo021Real28, traceTwo021Real29, traceTwo021Real30, traceTwo021Real31, traceTwo021Real32, traceTwo021Real33, traceTwo021Real34, traceTwo021Real35]
  rw [two_trace_recurrence ((realA z k)^2+(realB z k)^2+(realC z k)^2) (realB z k*(realA z k+realC z k)) (realA z k*realC z k) 15]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
