module

public import PackedPolynomialData
public import Scalar021VSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def vOrder021 (k : Fin 3) : Polynomial := scalarV021Step04 k

theorem eval_vOrder021 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder021 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 21 := by
  change SparsePolynomial.eval (evaluator z) (scalarV021Step04 k) = _
  rw [eval_scalarV021Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarVB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 20 -
    (SparsePolynomial.eval (evaluator z) (scalarVD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 19
  dsimp only [scalarV021Real01, scalarV021Real02, scalarV021Real03, scalarV021Real04]
  simp only [eval_scalarVD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
