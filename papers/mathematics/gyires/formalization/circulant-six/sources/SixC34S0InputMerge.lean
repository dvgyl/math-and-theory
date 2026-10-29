import SixC34S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC34S0InputPolynomial : Polynomial := rawDense
theorem SixC34S0Input_merge : orderedMerge 6188 SixC34S0InputLeftSorted SixC34S0InputRightSorted = SixC34S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC34S0Input_eval (f : ℕ →* ℝ) : eval f SixC34S0InputPolynomial = eval f (expandSlices 11 3 SixC34S0InputSlices) := by
  rw [← SixC34S0Input_merge, eval_orderedMerge, ← SixC34S0Input_left_sorted, ← SixC34S0Input_right_sorted, eval_sort, eval_sort, SixC34S0Input_flat, eval_append]
end SixCertificates
