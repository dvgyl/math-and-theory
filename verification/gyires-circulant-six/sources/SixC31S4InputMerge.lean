import SixC31S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC31S4InputPolynomial : Polynomial := SixC31S3OutputPolynomial
theorem SixC31S4Input_merge : orderedMerge 6188 SixC31S4InputLeftSorted SixC31S4InputRightSorted = SixC31S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC31S4Input_eval (f : ℕ →* ℝ) : eval f SixC31S4InputPolynomial = eval f (expandSlices 5 2 SixC31S4InputSlices) := by
  rw [← SixC31S4Input_merge, eval_orderedMerge, ← SixC31S4Input_left_sorted, ← SixC31S4Input_right_sorted, eval_sort, eval_sort, SixC31S4Input_flat, eval_append]
end SixCertificates
