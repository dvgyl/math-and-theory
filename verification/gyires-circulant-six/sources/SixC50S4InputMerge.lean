import SixC50S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC50S4InputPolynomial : Polynomial := SixC50S3OutputPolynomial
theorem SixC50S4Input_merge : orderedMerge 6188 SixC50S4InputLeftSorted SixC50S4InputRightSorted = SixC50S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC50S4Input_eval (f : ℕ →* ℝ) : eval f SixC50S4InputPolynomial = eval f (expandSlices 7 2 SixC50S4InputSlices) := by
  rw [← SixC50S4Input_merge, eval_orderedMerge, ← SixC50S4Input_left_sorted, ← SixC50S4Input_right_sorted, eval_sort, eval_sort, SixC50S4Input_flat, eval_append]
end SixCertificates
