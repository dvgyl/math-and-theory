module

public import Scalar015USteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def uOrder015 (k : Fin 3) : Polynomial := scalarU015Step04 k

theorem eval_uOrder015 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (uOrder015 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 15 := by
  change SparsePolynomial.eval (evaluator z) (scalarU015Step04 k) = _
  rw [eval_scalarU015Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarUB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 14 -
    (SparsePolynomial.eval (evaluator z) (scalarUD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 13
  dsimp only [scalarU015Real01, scalarU015Real02, scalarU015Real03, scalarU015Real04]
  simp only [eval_scalarUD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
