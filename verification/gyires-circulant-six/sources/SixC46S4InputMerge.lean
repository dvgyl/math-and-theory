import SixC46S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC46S4InputPolynomial : Polynomial := SixC46S3OutputPolynomial
theorem SixC46S4Input_merge : orderedMerge 6188 SixC46S4InputLeftSorted SixC46S4InputRightSorted = SixC46S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC46S4Input_eval (f : ℕ →* ℝ) : eval f SixC46S4InputPolynomial = eval f (expandSlices 5 2 SixC46S4InputSlices) := by
  rw [← SixC46S4Input_merge, eval_orderedMerge, ← SixC46S4Input_left_sorted, ← SixC46S4Input_right_sorted, eval_sort, eval_sort, SixC46S4Input_flat, eval_append]
end SixCertificates
