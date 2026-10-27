import SixC10S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC10S4InputPolynomial : Polynomial := SixC10S3OutputPolynomial
theorem SixC10S4Input_merge : orderedMerge 6188 SixC10S4InputLeftSorted SixC10S4InputRightSorted = SixC10S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC10S4Input_eval (f : ℕ →* ℝ) : eval f SixC10S4InputPolynomial = eval f (expandSlices 3 2 SixC10S4InputSlices) := by
  rw [← SixC10S4Input_merge, eval_orderedMerge, ← SixC10S4Input_left_sorted, ← SixC10S4Input_right_sorted, eval_sort, eval_sort, SixC10S4Input_flat, eval_append]
end SixCertificates
