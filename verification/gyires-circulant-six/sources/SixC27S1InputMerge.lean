import SixC27S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC27S1InputPolynomial : Polynomial := SixC27S0OutputPolynomial
theorem SixC27S1Input_merge : orderedMerge 6188 SixC27S1InputLeftSorted SixC27S1InputRightSorted = SixC27S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC27S1Input_eval (f : ℕ →* ℝ) : eval f SixC27S1InputPolynomial = eval f (expandSlices 13 11 SixC27S1InputSlices) := by
  rw [← SixC27S1Input_merge, eval_orderedMerge, ← SixC27S1Input_left_sorted, ← SixC27S1Input_right_sorted, eval_sort, eval_sort, SixC27S1Input_flat, eval_append]
end SixCertificates
