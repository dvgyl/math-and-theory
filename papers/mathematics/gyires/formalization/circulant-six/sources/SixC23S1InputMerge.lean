import SixC23S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC23S1InputPolynomial : Polynomial := SixC23S0OutputPolynomial
theorem SixC23S1Input_merge : orderedMerge 6188 SixC23S1InputLeftSorted SixC23S1InputRightSorted = SixC23S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC23S1Input_eval (f : ℕ →* ℝ) : eval f SixC23S1InputPolynomial = eval f (expandSlices 7 11 SixC23S1InputSlices) := by
  rw [← SixC23S1Input_merge, eval_orderedMerge, ← SixC23S1Input_left_sorted, ← SixC23S1Input_right_sorted, eval_sort, eval_sort, SixC23S1Input_flat, eval_append]
end SixCertificates
