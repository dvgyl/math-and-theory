import SixC58S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC58S2InputPolynomial : Polynomial := SixC58S1OutputPolynomial
theorem SixC58S2Input_merge : orderedMerge 6188 SixC58S2InputLeftSorted SixC58S2InputRightSorted = SixC58S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC58S2Input_eval (f : ℕ →* ℝ) : eval f SixC58S2InputPolynomial = eval f (expandSlices 13 5 SixC58S2InputSlices) := by
  rw [← SixC58S2Input_merge, eval_orderedMerge, ← SixC58S2Input_left_sorted, ← SixC58S2Input_right_sorted, eval_sort, eval_sort, SixC58S2Input_flat, eval_append]
end SixCertificates
