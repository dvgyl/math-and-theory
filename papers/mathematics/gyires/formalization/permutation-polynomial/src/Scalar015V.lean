module

public import Scalar015VSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def vOrder015 (k : Fin 3) : Polynomial := scalarV015Step04 k

theorem eval_vOrder015 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder015 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 15 := by
  change SparsePolynomial.eval (evaluator z) (scalarV015Step04 k) = _
  rw [eval_scalarV015Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarVB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 14 -
    (SparsePolynomial.eval (evaluator z) (scalarVD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 13
  dsimp only [scalarV015Real01, scalarV015Real02, scalarV015Real03, scalarV015Real04]
  simp only [eval_scalarVD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
