import SixC20S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC20S4InputPolynomial : Polynomial := SixC20S3OutputPolynomial
theorem SixC20S4Input_merge : orderedMerge 6188 SixC20S4InputLeftSorted SixC20S4InputRightSorted = SixC20S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC20S4Input_eval (f : ℕ →* ℝ) : eval f SixC20S4InputPolynomial = eval f (expandSlices 3 2 SixC20S4InputSlices) := by
  rw [← SixC20S4Input_merge, eval_orderedMerge, ← SixC20S4Input_left_sorted, ← SixC20S4Input_right_sorted, eval_sort, eval_sort, SixC20S4Input_flat, eval_append]
end SixCertificates
