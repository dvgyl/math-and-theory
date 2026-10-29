import SixC06S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC06S4InputPolynomial : Polynomial := SixC06S3OutputPolynomial
theorem SixC06S4Input_merge : orderedMerge 6188 SixC06S4InputLeftSorted SixC06S4InputRightSorted = SixC06S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC06S4Input_eval (f : ℕ →* ℝ) : eval f SixC06S4InputPolynomial = eval f (expandSlices 3 2 SixC06S4InputSlices) := by
  rw [← SixC06S4Input_merge, eval_orderedMerge, ← SixC06S4Input_left_sorted, ← SixC06S4Input_right_sorted, eval_sort, eval_sort, SixC06S4Input_flat, eval_append]
end SixCertificates
