module

public import Scalar020USteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def uOrder020 (k : Fin 3) : Polynomial := scalarU020Step04 k

theorem eval_uOrder020 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (uOrder020 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 20 := by
  change SparsePolynomial.eval (evaluator z) (scalarU020Step04 k) = _
  rw [eval_scalarU020Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarUB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 19 -
    (SparsePolynomial.eval (evaluator z) (scalarUD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 18
  dsimp only [scalarU020Real01, scalarU020Real02, scalarU020Real03, scalarU020Real04]
  simp only [eval_scalarUD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
