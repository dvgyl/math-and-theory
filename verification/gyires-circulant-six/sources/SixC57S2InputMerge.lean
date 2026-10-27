import SixC57S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC57S2InputPolynomial : Polynomial := SixC57S1OutputPolynomial
theorem SixC57S2Input_merge : orderedMerge 6188 SixC57S2InputLeftSorted SixC57S2InputRightSorted = SixC57S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC57S2Input_eval (f : ℕ →* ℝ) : eval f SixC57S2InputPolynomial = eval f (expandSlices 11 5 SixC57S2InputSlices) := by
  rw [← SixC57S2Input_merge, eval_orderedMerge, ← SixC57S2Input_left_sorted, ← SixC57S2Input_right_sorted, eval_sort, eval_sort, SixC57S2Input_flat, eval_append]
end SixCertificates
