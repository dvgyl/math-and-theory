module

public import Scalar015WSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def wOrder015 (k : Fin 3) : Polynomial := scalarW015Step04 k

theorem eval_wOrder015 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (wOrder015 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 15 := by
  change SparsePolynomial.eval (evaluator z) (scalarW015Step04 k) = _
  rw [eval_scalarW015Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarWB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 14 -
    (SparsePolynomial.eval (evaluator z) (scalarWD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 13
  dsimp only [scalarW015Real01, scalarW015Real02, scalarW015Real03, scalarW015Real04]
  simp only [eval_scalarWD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
