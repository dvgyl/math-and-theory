import SixC12S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC12S4InputPolynomial : Polynomial := SixC12S3OutputPolynomial
theorem SixC12S4Input_merge : orderedMerge 6188 SixC12S4InputLeftSorted SixC12S4InputRightSorted = SixC12S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC12S4Input_eval (f : ℕ →* ℝ) : eval f SixC12S4InputPolynomial = eval f (expandSlices 3 2 SixC12S4InputSlices) := by
  rw [← SixC12S4Input_merge, eval_orderedMerge, ← SixC12S4Input_left_sorted, ← SixC12S4Input_right_sorted, eval_sort, eval_sort, SixC12S4Input_flat, eval_append]
end SixCertificates
