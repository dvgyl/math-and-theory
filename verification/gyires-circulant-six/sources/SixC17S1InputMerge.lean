import SixC17S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC17S1InputPolynomial : Polynomial := SixC17S0OutputPolynomial
theorem SixC17S1Input_merge : orderedMerge 6188 SixC17S1InputLeftSorted SixC17S1InputRightSorted = SixC17S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC17S1Input_eval (f : ℕ →* ℝ) : eval f SixC17S1InputPolynomial = eval f (expandSlices 7 13 SixC17S1InputSlices) := by
  rw [← SixC17S1Input_merge, eval_orderedMerge, ← SixC17S1Input_left_sorted, ← SixC17S1Input_right_sorted, eval_sort, eval_sort, SixC17S1Input_flat, eval_append]
end SixCertificates
