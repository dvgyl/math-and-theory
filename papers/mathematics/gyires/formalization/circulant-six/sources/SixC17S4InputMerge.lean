import SixC17S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC17S4InputPolynomial : Polynomial := SixC17S3OutputPolynomial
theorem SixC17S4Input_merge : orderedMerge 6188 SixC17S4InputLeftSorted SixC17S4InputRightSorted = SixC17S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC17S4Input_eval (f : ℕ →* ℝ) : eval f SixC17S4InputPolynomial = eval f (expandSlices 3 2 SixC17S4InputSlices) := by
  rw [← SixC17S4Input_merge, eval_orderedMerge, ← SixC17S4Input_left_sorted, ← SixC17S4Input_right_sorted, eval_sort, eval_sort, SixC17S4Input_flat, eval_append]
end SixCertificates
