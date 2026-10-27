import SixC49S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC49S2InputPolynomial : Polynomial := SixC49S1OutputPolynomial
theorem SixC49S2Input_merge : orderedMerge 6188 SixC49S2InputLeftSorted SixC49S2InputRightSorted = SixC49S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC49S2Input_eval (f : ℕ →* ℝ) : eval f SixC49S2InputPolynomial = eval f (expandSlices 5 3 SixC49S2InputSlices) := by
  rw [← SixC49S2Input_merge, eval_orderedMerge, ← SixC49S2Input_left_sorted, ← SixC49S2Input_right_sorted, eval_sort, eval_sort, SixC49S2Input_flat, eval_append]
end SixCertificates
