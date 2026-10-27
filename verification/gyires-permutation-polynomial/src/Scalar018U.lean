module

public import Scalar018USteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def uOrder018 (k : Fin 3) : Polynomial := scalarU018Step04 k

theorem eval_uOrder018 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (uOrder018 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 18 := by
  change SparsePolynomial.eval (evaluator z) (scalarU018Step04 k) = _
  rw [eval_scalarU018Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarUB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 17 -
    (SparsePolynomial.eval (evaluator z) (scalarUD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 16
  dsimp only [scalarU018Real01, scalarU018Real02, scalarU018Real03, scalarU018Real04]
  simp only [eval_scalarUD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
