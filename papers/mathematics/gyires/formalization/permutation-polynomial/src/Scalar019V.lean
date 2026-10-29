module

public import Scalar019VSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def vOrder019 (k : Fin 3) : Polynomial := scalarV019Step04 k

theorem eval_vOrder019 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder019 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 19 := by
  change SparsePolynomial.eval (evaluator z) (scalarV019Step04 k) = _
  rw [eval_scalarV019Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarVB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 18 -
    (SparsePolynomial.eval (evaluator z) (scalarVD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k)) (SparsePolynomial.eval (evaluator z) (scalarVD k)) 17
  dsimp only [scalarV019Real01, scalarV019Real02, scalarV019Real03, scalarV019Real04]
  simp only [eval_scalarVD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
