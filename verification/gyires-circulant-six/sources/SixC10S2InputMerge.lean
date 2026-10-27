import SixC10S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC10S2InputPolynomial : Polynomial := SixC10S1OutputPolynomial
theorem SixC10S2Input_merge : orderedMerge 6188 SixC10S2InputLeftSorted SixC10S2InputRightSorted = SixC10S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC10S2Input_eval (f : ℕ →* ℝ) : eval f SixC10S2InputPolynomial = eval f (expandSlices 13 7 SixC10S2InputSlices) := by
  rw [← SixC10S2Input_merge, eval_orderedMerge, ← SixC10S2Input_left_sorted, ← SixC10S2Input_right_sorted, eval_sort, eval_sort, SixC10S2Input_flat, eval_append]
end SixCertificates
