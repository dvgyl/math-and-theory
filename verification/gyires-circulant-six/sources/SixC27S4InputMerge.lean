import SixC27S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC27S4InputPolynomial : Polynomial := SixC27S3OutputPolynomial
theorem SixC27S4Input_merge : orderedMerge 6188 SixC27S4InputLeftSorted SixC27S4InputRightSorted = SixC27S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC27S4Input_eval (f : ℕ →* ℝ) : eval f SixC27S4InputPolynomial = eval f (expandSlices 5 2 SixC27S4InputSlices) := by
  rw [← SixC27S4Input_merge, eval_orderedMerge, ← SixC27S4Input_left_sorted, ← SixC27S4Input_right_sorted, eval_sort, eval_sort, SixC27S4Input_flat, eval_append]
end SixCertificates
