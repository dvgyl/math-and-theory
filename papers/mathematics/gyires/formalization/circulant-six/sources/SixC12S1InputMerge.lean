import SixC12S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC12S1InputPolynomial : Polynomial := SixC12S0OutputPolynomial
theorem SixC12S1Input_merge : orderedMerge 6188 SixC12S1InputLeftSorted SixC12S1InputRightSorted = SixC12S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC12S1Input_eval (f : ℕ →* ℝ) : eval f SixC12S1InputPolynomial = eval f (expandSlices 7 5 SixC12S1InputSlices) := by
  rw [← SixC12S1Input_merge, eval_orderedMerge, ← SixC12S1Input_left_sorted, ← SixC12S1Input_right_sorted, eval_sort, eval_sort, SixC12S1Input_flat, eval_append]
end SixCertificates
