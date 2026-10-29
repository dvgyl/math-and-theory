import SixC34S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC34S2InputPolynomial : Polynomial := SixC34S1OutputPolynomial
theorem SixC34S2Input_merge : orderedMerge 6188 SixC34S2InputLeftSorted SixC34S2InputRightSorted = SixC34S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC34S2Input_eval (f : ℕ →* ℝ) : eval f SixC34S2InputPolynomial = eval f (expandSlices 13 7 SixC34S2InputSlices) := by
  rw [← SixC34S2Input_merge, eval_orderedMerge, ← SixC34S2Input_left_sorted, ← SixC34S2Input_right_sorted, eval_sort, eval_sort, SixC34S2Input_flat, eval_append]
end SixCertificates
