import SixC36S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC36S4InputPolynomial : Polynomial := SixC36S3OutputPolynomial
theorem SixC36S4Input_merge : orderedMerge 6188 SixC36S4InputLeftSorted SixC36S4InputRightSorted = SixC36S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC36S4Input_eval (f : ℕ →* ℝ) : eval f SixC36S4InputPolynomial = eval f (expandSlices 5 2 SixC36S4InputSlices) := by
  rw [← SixC36S4Input_merge, eval_orderedMerge, ← SixC36S4Input_left_sorted, ← SixC36S4Input_right_sorted, eval_sort, eval_sort, SixC36S4Input_flat, eval_append]
end SixCertificates
