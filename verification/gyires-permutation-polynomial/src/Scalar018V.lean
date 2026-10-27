module

public import Scalar018VSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def vOrder018 (k : Fin 3) : Polynomial := scalarV018Step04 k

theorem eval_vOrder018 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder018 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 18 := by
  change SparsePolynomial.eval (evaluator z) (scalarV018Step04 k) = _
  rw [eval_scalarV018Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarVB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 17 -
    (SparsePolynomial.eval (evaluator z) (scalarVD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 16
  dsimp only [scalarV018Real01, scalarV018Real02, scalarV018Real03, scalarV018Real04]
  simp only [eval_scalarVD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
