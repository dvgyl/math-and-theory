import SixC56S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC56S1InputPolynomial : Polynomial := SixC56S0OutputPolynomial
theorem SixC56S1Input_merge : orderedMerge 6188 SixC56S1InputLeftSorted SixC56S1InputRightSorted = SixC56S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC56S1Input_eval (f : ℕ →* ℝ) : eval f SixC56S1InputPolynomial = eval f (expandSlices 3 11 SixC56S1InputSlices) := by
  rw [← SixC56S1Input_merge, eval_orderedMerge, ← SixC56S1Input_left_sorted, ← SixC56S1Input_right_sorted, eval_sort, eval_sort, SixC56S1Input_flat, eval_append]
end SixCertificates
