module

public import PackedPolynomialData
public import Scalar022WSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def wOrder022 (k : Fin 3) : Polynomial := scalarW022Step04 k

theorem eval_wOrder022 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (wOrder022 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 22 := by
  change SparsePolynomial.eval (evaluator z) (scalarW022Step04 k) = _
  rw [eval_scalarW022Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarWB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 21 -
    (SparsePolynomial.eval (evaluator z) (scalarWD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 20
  dsimp only [scalarW022Real01, scalarW022Real02, scalarW022Real03, scalarW022Real04]
  simp only [eval_scalarWD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
