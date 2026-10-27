import SixC18S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC18S4InputPolynomial : Polynomial := SixC18S3OutputPolynomial
theorem SixC18S4Input_merge : orderedMerge 6188 SixC18S4InputLeftSorted SixC18S4InputRightSorted = SixC18S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC18S4Input_eval (f : ℕ →* ℝ) : eval f SixC18S4InputPolynomial = eval f (expandSlices 3 2 SixC18S4InputSlices) := by
  rw [← SixC18S4Input_merge, eval_orderedMerge, ← SixC18S4Input_left_sorted, ← SixC18S4Input_right_sorted, eval_sort, eval_sort, SixC18S4Input_flat, eval_append]
end SixCertificates
