import SixC47S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC47S4InputPolynomial : Polynomial := SixC47S3OutputPolynomial
theorem SixC47S4Input_merge : orderedMerge 6188 SixC47S4InputLeftSorted SixC47S4InputRightSorted = SixC47S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC47S4Input_eval (f : ℕ →* ℝ) : eval f SixC47S4InputPolynomial = eval f (expandSlices 5 2 SixC47S4InputSlices) := by
  rw [← SixC47S4Input_merge, eval_orderedMerge, ← SixC47S4Input_left_sorted, ← SixC47S4Input_right_sorted, eval_sort, eval_sort, SixC47S4Input_flat, eval_append]
end SixCertificates
