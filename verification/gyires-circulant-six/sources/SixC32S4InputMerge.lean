import SixC32S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC32S4InputPolynomial : Polynomial := SixC32S3OutputPolynomial
theorem SixC32S4Input_merge : orderedMerge 6188 SixC32S4InputLeftSorted SixC32S4InputRightSorted = SixC32S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC32S4Input_eval (f : ℕ →* ℝ) : eval f SixC32S4InputPolynomial = eval f (expandSlices 5 2 SixC32S4InputSlices) := by
  rw [← SixC32S4Input_merge, eval_orderedMerge, ← SixC32S4Input_left_sorted, ← SixC32S4Input_right_sorted, eval_sort, eval_sort, SixC32S4Input_flat, eval_append]
end SixCertificates
