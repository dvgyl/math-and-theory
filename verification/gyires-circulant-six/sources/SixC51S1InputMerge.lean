import SixC51S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC51S1InputPolynomial : Polynomial := SixC51S0OutputPolynomial
theorem SixC51S1Input_merge : orderedMerge 6188 SixC51S1InputLeftSorted SixC51S1InputRightSorted = SixC51S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC51S1Input_eval (f : ℕ →* ℝ) : eval f SixC51S1InputPolynomial = eval f (expandSlices 13 11 SixC51S1InputSlices) := by
  rw [← SixC51S1Input_merge, eval_orderedMerge, ← SixC51S1Input_left_sorted, ← SixC51S1Input_right_sorted, eval_sort, eval_sort, SixC51S1Input_flat, eval_append]
end SixCertificates
