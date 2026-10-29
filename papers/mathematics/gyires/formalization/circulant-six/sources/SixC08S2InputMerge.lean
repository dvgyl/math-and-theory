import SixC08S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC08S2InputPolynomial : Polynomial := SixC08S1OutputPolynomial
theorem SixC08S2Input_merge : orderedMerge 6188 SixC08S2InputLeftSorted SixC08S2InputRightSorted = SixC08S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC08S2Input_eval (f : ℕ →* ℝ) : eval f SixC08S2InputPolynomial = eval f (expandSlices 11 7 SixC08S2InputSlices) := by
  rw [← SixC08S2Input_merge, eval_orderedMerge, ← SixC08S2Input_left_sorted, ← SixC08S2Input_right_sorted, eval_sort, eval_sort, SixC08S2Input_flat, eval_append]
end SixCertificates
