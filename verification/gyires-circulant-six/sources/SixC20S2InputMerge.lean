import SixC20S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC20S2InputPolynomial : Polynomial := SixC20S1OutputPolynomial
theorem SixC20S2Input_merge : orderedMerge 6188 SixC20S2InputLeftSorted SixC20S2InputRightSorted = SixC20S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC20S2Input_eval (f : ℕ →* ℝ) : eval f SixC20S2InputPolynomial = eval f (expandSlices 7 13 SixC20S2InputSlices) := by
  rw [← SixC20S2Input_merge, eval_orderedMerge, ← SixC20S2Input_left_sorted, ← SixC20S2Input_right_sorted, eval_sort, eval_sort, SixC20S2Input_flat, eval_append]
end SixCertificates
