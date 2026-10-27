import SixC47S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC47S2InputPolynomial : Polynomial := SixC47S1OutputPolynomial
theorem SixC47S2Input_merge : orderedMerge 6188 SixC47S2InputLeftSorted SixC47S2InputRightSorted = SixC47S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC47S2Input_eval (f : ℕ →* ℝ) : eval f SixC47S2InputPolynomial = eval f (expandSlices 11 13 SixC47S2InputSlices) := by
  rw [← SixC47S2Input_merge, eval_orderedMerge, ← SixC47S2Input_left_sorted, ← SixC47S2Input_right_sorted, eval_sort, eval_sort, SixC47S2Input_flat, eval_append]
end SixCertificates
