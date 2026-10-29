import SixC23S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC23S2InputPolynomial : Polynomial := SixC23S1OutputPolynomial
theorem SixC23S2Input_merge : orderedMerge 6188 SixC23S2InputLeftSorted SixC23S2InputRightSorted = SixC23S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC23S2Input_eval (f : ℕ →* ℝ) : eval f SixC23S2InputPolynomial = eval f (expandSlices 11 13 SixC23S2InputSlices) := by
  rw [← SixC23S2Input_merge, eval_orderedMerge, ← SixC23S2Input_left_sorted, ← SixC23S2Input_right_sorted, eval_sort, eval_sort, SixC23S2Input_flat, eval_append]
end SixCertificates
