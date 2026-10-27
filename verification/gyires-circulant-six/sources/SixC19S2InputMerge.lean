import SixC19S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC19S2InputPolynomial : Polynomial := SixC19S1OutputPolynomial
theorem SixC19S2Input_merge : orderedMerge 6188 SixC19S2InputLeftSorted SixC19S2InputRightSorted = SixC19S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC19S2Input_eval (f : ℕ →* ℝ) : eval f SixC19S2InputPolynomial = eval f (expandSlices 5 13 SixC19S2InputSlices) := by
  rw [← SixC19S2Input_merge, eval_orderedMerge, ← SixC19S2Input_left_sorted, ← SixC19S2Input_right_sorted, eval_sort, eval_sort, SixC19S2Input_flat, eval_append]
end SixCertificates
