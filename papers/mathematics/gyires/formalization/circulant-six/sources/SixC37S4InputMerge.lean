import SixC37S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC37S4InputPolynomial : Polynomial := SixC37S3OutputPolynomial
theorem SixC37S4Input_merge : orderedMerge 6188 SixC37S4InputLeftSorted SixC37S4InputRightSorted = SixC37S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC37S4Input_eval (f : ℕ →* ℝ) : eval f SixC37S4InputPolynomial = eval f (expandSlices 5 2 SixC37S4InputSlices) := by
  rw [← SixC37S4Input_merge, eval_orderedMerge, ← SixC37S4Input_left_sorted, ← SixC37S4Input_right_sorted, eval_sort, eval_sort, SixC37S4Input_flat, eval_append]
end SixCertificates
