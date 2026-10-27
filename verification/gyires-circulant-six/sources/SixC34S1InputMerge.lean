import SixC34S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC34S1InputPolynomial : Polynomial := SixC34S0OutputPolynomial
theorem SixC34S1Input_merge : orderedMerge 6188 SixC34S1InputLeftSorted SixC34S1InputRightSorted = SixC34S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC34S1Input_eval (f : ℕ →* ℝ) : eval f SixC34S1InputPolynomial = eval f (expandSlices 3 13 SixC34S1InputSlices) := by
  rw [← SixC34S1Input_merge, eval_orderedMerge, ← SixC34S1Input_left_sorted, ← SixC34S1Input_right_sorted, eval_sort, eval_sort, SixC34S1Input_flat, eval_append]
end SixCertificates
