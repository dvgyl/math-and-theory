import SixC48S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC48S4InputPolynomial : Polynomial := SixC48S3OutputPolynomial
theorem SixC48S4Input_merge : orderedMerge 6188 SixC48S4InputLeftSorted SixC48S4InputRightSorted = SixC48S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC48S4Input_eval (f : ℕ →* ℝ) : eval f SixC48S4InputPolynomial = eval f (expandSlices 7 2 SixC48S4InputSlices) := by
  rw [← SixC48S4Input_merge, eval_orderedMerge, ← SixC48S4Input_left_sorted, ← SixC48S4Input_right_sorted, eval_sort, eval_sort, SixC48S4Input_flat, eval_append]
end SixCertificates
