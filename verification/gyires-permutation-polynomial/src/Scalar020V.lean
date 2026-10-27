module

public import Scalar020VSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def vOrder020 (k : Fin 3) : Polynomial := scalarV020Step04 k

theorem eval_vOrder020 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder020 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 20 := by
  change SparsePolynomial.eval (evaluator z) (scalarV020Step04 k) = _
  rw [eval_scalarV020Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarVB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 19 -
    (SparsePolynomial.eval (evaluator z) (scalarVD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 18
  dsimp only [scalarV020Real01, scalarV020Real02, scalarV020Real03, scalarV020Real04]
  simp only [eval_scalarVD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
