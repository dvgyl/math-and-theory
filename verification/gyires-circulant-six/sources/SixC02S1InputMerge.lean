import SixC02S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC02S1InputPolynomial : Polynomial := SixC02S0OutputPolynomial
theorem SixC02S1Input_merge : orderedMerge 6188 SixC02S1InputLeftSorted SixC02S1InputRightSorted = SixC02S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC02S1Input_eval (f : ℕ →* ℝ) : eval f SixC02S1InputPolynomial = eval f (expandSlices 7 11 SixC02S1InputSlices) := by
  rw [← SixC02S1Input_merge, eval_orderedMerge, ← SixC02S1Input_left_sorted, ← SixC02S1Input_right_sorted, eval_sort, eval_sort, SixC02S1Input_flat, eval_append]
end SixCertificates
