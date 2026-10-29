import SixC10S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC10S1InputPolynomial : Polynomial := SixC10S0OutputPolynomial
theorem SixC10S1Input_merge : orderedMerge 6188 SixC10S1InputLeftSorted SixC10S1InputRightSorted = SixC10S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC10S1Input_eval (f : ℕ →* ℝ) : eval f SixC10S1InputPolynomial = eval f (expandSlices 5 13 SixC10S1InputSlices) := by
  rw [← SixC10S1Input_merge, eval_orderedMerge, ← SixC10S1Input_left_sorted, ← SixC10S1Input_right_sorted, eval_sort, eval_sort, SixC10S1Input_flat, eval_append]
end SixCertificates
