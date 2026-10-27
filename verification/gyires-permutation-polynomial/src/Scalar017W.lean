module

public import Scalar017WSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def wOrder017 (k : Fin 3) : Polynomial := scalarW017Step04 k

theorem eval_wOrder017 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (wOrder017 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 17 := by
  change SparsePolynomial.eval (evaluator z) (scalarW017Step04 k) = _
  rw [eval_scalarW017Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarWB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 16 -
    (SparsePolynomial.eval (evaluator z) (scalarWD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 15
  dsimp only [scalarW017Real01, scalarW017Real02, scalarW017Real03, scalarW017Real04]
  simp only [eval_scalarWD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
