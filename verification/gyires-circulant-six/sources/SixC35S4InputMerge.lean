import SixC35S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC35S4InputPolynomial : Polynomial := SixC35S3OutputPolynomial
theorem SixC35S4Input_merge : orderedMerge 6188 SixC35S4InputLeftSorted SixC35S4InputRightSorted = SixC35S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC35S4Input_eval (f : ℕ →* ℝ) : eval f SixC35S4InputPolynomial = eval f (expandSlices 5 2 SixC35S4InputSlices) := by
  rw [← SixC35S4Input_merge, eval_orderedMerge, ← SixC35S4Input_left_sorted, ← SixC35S4Input_right_sorted, eval_sort, eval_sort, SixC35S4Input_flat, eval_append]
end SixCertificates
