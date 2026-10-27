module

public import Scalar016WSteps

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def wOrder016 (k : Fin 3) : Polynomial := scalarW016Step04 k

theorem eval_wOrder016 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (wOrder016 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 16 := by
  change SparsePolynomial.eval (evaluator z) (scalarW016Step04 k) = _
  rw [eval_scalarW016Step04]
  change _ = (SparsePolynomial.eval (evaluator z) (scalarWB k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 15 -
    (SparsePolynomial.eval (evaluator z) (scalarWD k)) * powerSum (SparsePolynomial.eval (evaluator z) (scalarWB k)) (SparsePolynomial.eval (evaluator z) (scalarWD k)) 14
  dsimp only [scalarW016Real01, scalarW016Real02, scalarW016Real03, scalarW016Real04]
  simp only [eval_scalarWD]
  ring

end MathAndTheory.Gyires.PermutationCoefficientStage
