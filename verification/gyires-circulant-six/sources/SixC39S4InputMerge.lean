import SixC39S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC39S4InputPolynomial : Polynomial := SixC39S3OutputPolynomial
theorem SixC39S4Input_merge : orderedMerge 6188 SixC39S4InputLeftSorted SixC39S4InputRightSorted = SixC39S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC39S4Input_eval (f : ℕ →* ℝ) : eval f SixC39S4InputPolynomial = eval f (expandSlices 5 2 SixC39S4InputSlices) := by
  rw [← SixC39S4Input_merge, eval_orderedMerge, ← SixC39S4Input_left_sorted, ← SixC39S4Input_right_sorted, eval_sort, eval_sort, SixC39S4Input_flat, eval_append]
end SixCertificates
