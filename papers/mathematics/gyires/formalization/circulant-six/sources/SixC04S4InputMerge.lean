import SixC04S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC04S4InputPolynomial : Polynomial := SixC04S3OutputPolynomial
theorem SixC04S4Input_merge : orderedMerge 6188 SixC04S4InputLeftSorted SixC04S4InputRightSorted = SixC04S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC04S4Input_eval (f : ℕ →* ℝ) : eval f SixC04S4InputPolynomial = eval f (expandSlices 3 2 SixC04S4InputSlices) := by
  rw [← SixC04S4Input_merge, eval_orderedMerge, ← SixC04S4Input_left_sorted, ← SixC04S4Input_right_sorted, eval_sort, eval_sort, SixC04S4Input_flat, eval_append]
end SixCertificates
