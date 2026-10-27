import SixC52S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC52S4InputPolynomial : Polynomial := SixC52S3OutputPolynomial
theorem SixC52S4Input_merge : orderedMerge 6188 SixC52S4InputLeftSorted SixC52S4InputRightSorted = SixC52S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC52S4Input_eval (f : ℕ →* ℝ) : eval f SixC52S4InputPolynomial = eval f (expandSlices 7 2 SixC52S4InputSlices) := by
  rw [← SixC52S4Input_merge, eval_orderedMerge, ← SixC52S4Input_left_sorted, ← SixC52S4Input_right_sorted, eval_sort, eval_sort, SixC52S4Input_flat, eval_append]
end SixCertificates
