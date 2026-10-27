import SixC43S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC43S4InputPolynomial : Polynomial := SixC43S3OutputPolynomial
theorem SixC43S4Input_merge : orderedMerge 6188 SixC43S4InputLeftSorted SixC43S4InputRightSorted = SixC43S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC43S4Input_eval (f : ℕ →* ℝ) : eval f SixC43S4InputPolynomial = eval f (expandSlices 5 2 SixC43S4InputSlices) := by
  rw [← SixC43S4Input_merge, eval_orderedMerge, ← SixC43S4Input_left_sorted, ← SixC43S4Input_right_sorted, eval_sort, eval_sort, SixC43S4Input_flat, eval_append]
end SixCertificates
