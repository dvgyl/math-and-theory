import SixC55S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC55S4InputPolynomial : Polynomial := SixC55S3OutputPolynomial
theorem SixC55S4Input_merge : orderedMerge 6188 SixC55S4InputLeftSorted SixC55S4InputRightSorted = SixC55S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC55S4Input_eval (f : ℕ →* ℝ) : eval f SixC55S4InputPolynomial = eval f (expandSlices 7 2 SixC55S4InputSlices) := by
  rw [← SixC55S4Input_merge, eval_orderedMerge, ← SixC55S4Input_left_sorted, ← SixC55S4Input_right_sorted, eval_sort, eval_sort, SixC55S4Input_flat, eval_append]
end SixCertificates
