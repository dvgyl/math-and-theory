import SixC14S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC14S4InputPolynomial : Polynomial := SixC14S3OutputPolynomial
theorem SixC14S4Input_merge : orderedMerge 6188 SixC14S4InputLeftSorted SixC14S4InputRightSorted = SixC14S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC14S4Input_eval (f : ℕ →* ℝ) : eval f SixC14S4InputPolynomial = eval f (expandSlices 3 2 SixC14S4InputSlices) := by
  rw [← SixC14S4Input_merge, eval_orderedMerge, ← SixC14S4Input_left_sorted, ← SixC14S4Input_right_sorted, eval_sort, eval_sort, SixC14S4Input_flat, eval_append]
end SixCertificates
