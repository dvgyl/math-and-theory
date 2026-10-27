import SixC12S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC12S2InputPolynomial : Polynomial := SixC12S1OutputPolynomial
theorem SixC12S2Input_merge : orderedMerge 6188 SixC12S2InputLeftSorted SixC12S2InputRightSorted = SixC12S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC12S2Input_eval (f : ℕ →* ℝ) : eval f SixC12S2InputPolynomial = eval f (expandSlices 5 11 SixC12S2InputSlices) := by
  rw [← SixC12S2Input_merge, eval_orderedMerge, ← SixC12S2Input_left_sorted, ← SixC12S2Input_right_sorted, eval_sort, eval_sort, SixC12S2Input_flat, eval_append]
end SixCertificates
