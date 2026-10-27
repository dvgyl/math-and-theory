import SixC34S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC34S4InputPolynomial : Polynomial := SixC34S3OutputPolynomial
theorem SixC34S4Input_merge : orderedMerge 6188 SixC34S4InputLeftSorted SixC34S4InputRightSorted = SixC34S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC34S4Input_eval (f : ℕ →* ℝ) : eval f SixC34S4InputPolynomial = eval f (expandSlices 5 2 SixC34S4InputSlices) := by
  rw [← SixC34S4Input_merge, eval_orderedMerge, ← SixC34S4Input_left_sorted, ← SixC34S4Input_right_sorted, eval_sort, eval_sort, SixC34S4Input_flat, eval_append]
end SixCertificates
