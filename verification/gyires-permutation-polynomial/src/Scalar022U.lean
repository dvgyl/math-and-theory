module

public import PackedPolynomialData
public import Scalar022USteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def uOrder022 (k : Fin 3) : Polynomial := scalarU022Step04 k

theorem eval_uOrder022 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (uOrder022 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 22 := by
  change SparsePolynomial.eval (evaluator z) (scalarU022Step04 k) = _
  rw [eval_scalarU022Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarUB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 21 -
    (SparsePolynomial.eval (evaluator z) (scalarUD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarUB k)) (SparsePolynomial.eval (evaluator z) (scalarUD k)) 20
  dsimp only [scalarU022Real01, scalarU022Real02, scalarU022Real03, scalarU022Real04]
  simp only [eval_scalarUD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
