import SixC38S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC38S2InputPolynomial : Polynomial := SixC38S1OutputPolynomial
theorem SixC38S2Input_merge : orderedMerge 6188 SixC38S2InputLeftSorted SixC38S2InputRightSorted = SixC38S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC38S2Input_eval (f : ℕ →* ℝ) : eval f SixC38S2InputPolynomial = eval f (expandSlices 7 11 SixC38S2InputSlices) := by
  rw [← SixC38S2Input_merge, eval_orderedMerge, ← SixC38S2Input_left_sorted, ← SixC38S2Input_right_sorted, eval_sort, eval_sort, SixC38S2Input_flat, eval_append]
end SixCertificates
