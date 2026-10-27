import SixC37S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC37S1InputPolynomial : Polynomial := SixC37S0OutputPolynomial
theorem SixC37S1Input_merge : orderedMerge 6188 SixC37S1InputLeftSorted SixC37S1InputRightSorted = SixC37S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC37S1Input_eval (f : ℕ →* ℝ) : eval f SixC37S1InputPolynomial = eval f (expandSlices 13 3 SixC37S1InputSlices) := by
  rw [← SixC37S1Input_merge, eval_orderedMerge, ← SixC37S1Input_left_sorted, ← SixC37S1Input_right_sorted, eval_sort, eval_sort, SixC37S1Input_flat, eval_append]
end SixCertificates
