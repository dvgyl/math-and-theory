import SixC53S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC53S4InputPolynomial : Polynomial := SixC53S3OutputPolynomial
theorem SixC53S4Input_merge : orderedMerge 6188 SixC53S4InputLeftSorted SixC53S4InputRightSorted = SixC53S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC53S4Input_eval (f : ℕ →* ℝ) : eval f SixC53S4InputPolynomial = eval f (expandSlices 7 2 SixC53S4InputSlices) := by
  rw [← SixC53S4Input_merge, eval_orderedMerge, ← SixC53S4Input_left_sorted, ← SixC53S4Input_right_sorted, eval_sort, eval_sort, SixC53S4Input_flat, eval_append]
end SixCertificates
