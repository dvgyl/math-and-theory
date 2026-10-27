import SixC55S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC55S1InputPolynomial : Polynomial := SixC55S0OutputPolynomial
theorem SixC55S1Input_merge : orderedMerge 6188 SixC55S1InputLeftSorted SixC55S1InputRightSorted = SixC55S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC55S1Input_eval (f : ℕ →* ℝ) : eval f SixC55S1InputPolynomial = eval f (expandSlices 13 3 SixC55S1InputSlices) := by
  rw [← SixC55S1Input_merge, eval_orderedMerge, ← SixC55S1Input_left_sorted, ← SixC55S1Input_right_sorted, eval_sort, eval_sort, SixC55S1Input_flat, eval_append]
end SixCertificates
