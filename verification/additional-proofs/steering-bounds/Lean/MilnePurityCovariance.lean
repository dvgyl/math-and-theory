import MilneDefs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- The conditional collision-purity polynomial, without normalization or
positivity assumptions. -/
def purityDifference (M : CMatrix) : ℂ :=
  Matrix.trace (M*M) - Matrix.trace (partialA M * partialA M)

def bobBlock (M : CMatrix) (a c : Q) : Matrix Q Q ℂ :=
  fun b d => M (a,b) (c,d)

/-- The polarized two-dimensional determinant identity. -/
theorem qubit_trace_covariance (A B F : Matrix Q Q ℂ) :
    Matrix.trace ((F*A*F)*(F*B*F)) -
        Matrix.trace (F*A*F) * Matrix.trace (F*B*F) =
      F.det ^ 2 * (Matrix.trace (A*B) - Matrix.trace A * Matrix.trace B) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem purityDifference_blocks (M : CMatrix) :
    purityDifference M = ∑ a, ∑ c,
      (Matrix.trace (bobBlock M a c * bobBlock M c a) -
        Matrix.trace (bobBlock M a c) * Matrix.trace (bobBlock M c a)) := by
  simp only [purityDifference, bobBlock, partialA, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem bobBlock_filter (M : CMatrix) (F : Matrix Q Q ℂ) (a c : Q) :
    bobBlock (onBob F * M * onBob F) a c = F * bobBlock M a c * F := by
  ext b d
  fin_cases a <;> fin_cases c <;>
    simp [bobBlock, onBob, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Exact covariance under a Bob filter. This is a polynomial identity on
actual complex matrices and is valid even for singular filters. -/
theorem purityDifference_filter (M : CMatrix) (F : Matrix Q Q ℂ) :
    purityDifference (onBob F * M * onBob F) = F.det ^ 2 * purityDifference M := by
  rw [purityDifference_blocks, purityDifference_blocks]
  simp_rw [bobBlock_filter, qubit_trace_covariance]
  simp only [Finset.mul_sum]

end Milne
