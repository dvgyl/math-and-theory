import SixC56S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC56S4InputPolynomial : Polynomial := SixC56S3OutputPolynomial
theorem SixC56S4Input_merge : orderedMerge 6188 SixC56S4InputLeftSorted SixC56S4InputRightSorted = SixC56S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC56S4Input_eval (f : ℕ →* ℝ) : eval f SixC56S4InputPolynomial = eval f (expandSlices 7 2 SixC56S4InputSlices) := by
  rw [← SixC56S4Input_merge, eval_orderedMerge, ← SixC56S4Input_left_sorted, ← SixC56S4Input_right_sorted, eval_sort, eval_sort, SixC56S4Input_flat, eval_append]
end SixCertificates
