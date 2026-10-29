import SixC29S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC29S4InputPolynomial : Polynomial := SixC29S3OutputPolynomial
theorem SixC29S4Input_merge : orderedMerge 6188 SixC29S4InputLeftSorted SixC29S4InputRightSorted = SixC29S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC29S4Input_eval (f : ℕ →* ℝ) : eval f SixC29S4InputPolynomial = eval f (expandSlices 5 2 SixC29S4InputSlices) := by
  rw [← SixC29S4Input_merge, eval_orderedMerge, ← SixC29S4Input_left_sorted, ← SixC29S4Input_right_sorted, eval_sort, eval_sort, SixC29S4Input_flat, eval_append]
end SixCertificates
