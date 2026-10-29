import SixC02S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC02S2InputPolynomial : Polynomial := SixC02S1OutputPolynomial
theorem SixC02S2Input_merge : orderedMerge 6188 SixC02S2InputLeftSorted SixC02S2InputRightSorted = SixC02S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC02S2Input_eval (f : ℕ →* ℝ) : eval f SixC02S2InputPolynomial = eval f (expandSlices 11 5 SixC02S2InputSlices) := by
  rw [← SixC02S2Input_merge, eval_orderedMerge, ← SixC02S2Input_left_sorted, ← SixC02S2Input_right_sorted, eval_sort, eval_sort, SixC02S2Input_flat, eval_append]
end SixCertificates
