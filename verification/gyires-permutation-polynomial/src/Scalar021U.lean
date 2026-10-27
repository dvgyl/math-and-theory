module

public import PackedPolynomialData
public import Scalar021USteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def uOrder021 (k : Fin 3) : Polynomial := scalarU021Step04 k

theorem eval_uOrder021 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (uOrder021 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 21 := by
  change SparsePolynomial.eval (evaluator z) (scalarU021Step04 k) = _
  rw [eval_scalarU021Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarUB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 20 -
    (SparsePolynomial.eval (evaluator z) (scalarUD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 19
  dsimp only [scalarU021Real01, scalarU021Real02, scalarU021Real03, scalarU021Real04]
  simp only [eval_scalarUD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
