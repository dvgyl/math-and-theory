import SixC54S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC54S2InputPolynomial : Polynomial := SixC54S1OutputPolynomial
theorem SixC54S2Input_merge : orderedMerge 6188 SixC54S2InputLeftSorted SixC54S2InputRightSorted = SixC54S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC54S2Input_eval (f : ℕ →* ℝ) : eval f SixC54S2InputPolynomial = eval f (expandSlices 3 5 SixC54S2InputSlices) := by
  rw [← SixC54S2Input_merge, eval_orderedMerge, ← SixC54S2Input_left_sorted, ← SixC54S2Input_right_sorted, eval_sort, eval_sort, SixC54S2Input_flat, eval_append]
end SixCertificates
