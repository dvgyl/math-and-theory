import SixC42S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC42S4InputPolynomial : Polynomial := SixC42S3OutputPolynomial
theorem SixC42S4Input_merge : orderedMerge 6188 SixC42S4InputLeftSorted SixC42S4InputRightSorted = SixC42S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC42S4Input_eval (f : ℕ →* ℝ) : eval f SixC42S4InputPolynomial = eval f (expandSlices 5 2 SixC42S4InputSlices) := by
  rw [← SixC42S4Input_merge, eval_orderedMerge, ← SixC42S4Input_left_sorted, ← SixC42S4Input_right_sorted, eval_sort, eval_sort, SixC42S4Input_flat, eval_append]
end SixCertificates
