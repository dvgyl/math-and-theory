import SixC24S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC24S4InputPolynomial : Polynomial := SixC24S3OutputPolynomial
theorem SixC24S4Input_merge : orderedMerge 6188 SixC24S4InputLeftSorted SixC24S4InputRightSorted = SixC24S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC24S4Input_eval (f : ℕ →* ℝ) : eval f SixC24S4InputPolynomial = eval f (expandSlices 5 2 SixC24S4InputSlices) := by
  rw [← SixC24S4Input_merge, eval_orderedMerge, ← SixC24S4Input_left_sorted, ← SixC24S4Input_right_sorted, eval_sort, eval_sort, SixC24S4Input_flat, eval_append]
end SixCertificates
