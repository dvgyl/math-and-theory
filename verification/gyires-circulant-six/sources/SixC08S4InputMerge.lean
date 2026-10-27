import SixC08S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC08S4InputPolynomial : Polynomial := SixC08S3OutputPolynomial
theorem SixC08S4Input_merge : orderedMerge 6188 SixC08S4InputLeftSorted SixC08S4InputRightSorted = SixC08S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC08S4Input_eval (f : ℕ →* ℝ) : eval f SixC08S4InputPolynomial = eval f (expandSlices 3 2 SixC08S4InputSlices) := by
  rw [← SixC08S4Input_merge, eval_orderedMerge, ← SixC08S4Input_left_sorted, ← SixC08S4Input_right_sorted, eval_sort, eval_sort, SixC08S4Input_flat, eval_append]
end SixCertificates
