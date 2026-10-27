module

public import Scalar020WSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def wOrder020 (k : Fin 3) : Polynomial := scalarW020Step04 k

theorem eval_wOrder020 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (wOrder020 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 20 := by
  change SparsePolynomial.eval (evaluator z) (scalarW020Step04 k) = _
  rw [eval_scalarW020Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarWB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 19 -
    (SparsePolynomial.eval (evaluator z) (scalarWD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 18
  dsimp only [scalarW020Real01, scalarW020Real02, scalarW020Real03, scalarW020Real04]
  simp only [eval_scalarWD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
