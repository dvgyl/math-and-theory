import SixC51S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC51S2InputPolynomial : Polynomial := SixC51S1OutputPolynomial
theorem SixC51S2Input_merge : orderedMerge 6188 SixC51S2InputLeftSorted SixC51S2InputRightSorted = SixC51S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC51S2Input_eval (f : ℕ →* ℝ) : eval f SixC51S2InputPolynomial = eval f (expandSlices 11 3 SixC51S2InputSlices) := by
  rw [← SixC51S2Input_merge, eval_orderedMerge, ← SixC51S2Input_left_sorted, ← SixC51S2Input_right_sorted, eval_sort, eval_sort, SixC51S2Input_flat, eval_append]
end SixCertificates
