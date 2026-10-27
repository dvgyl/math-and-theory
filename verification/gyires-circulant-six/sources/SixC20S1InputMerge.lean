import SixC20S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC20S1InputPolynomial : Polynomial := SixC20S0OutputPolynomial
theorem SixC20S1Input_merge : orderedMerge 6188 SixC20S1InputLeftSorted SixC20S1InputRightSorted = SixC20S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC20S1Input_eval (f : ℕ →* ℝ) : eval f SixC20S1InputPolynomial = eval f (expandSlices 5 7 SixC20S1InputSlices) := by
  rw [← SixC20S1Input_merge, eval_orderedMerge, ← SixC20S1Input_left_sorted, ← SixC20S1Input_right_sorted, eval_sort, eval_sort, SixC20S1Input_flat, eval_append]
end SixCertificates
