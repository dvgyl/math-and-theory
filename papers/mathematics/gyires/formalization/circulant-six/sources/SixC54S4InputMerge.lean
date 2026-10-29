import SixC54S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC54S4InputPolynomial : Polynomial := SixC54S3OutputPolynomial
theorem SixC54S4Input_merge : orderedMerge 6188 SixC54S4InputLeftSorted SixC54S4InputRightSorted = SixC54S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC54S4Input_eval (f : ℕ →* ℝ) : eval f SixC54S4InputPolynomial = eval f (expandSlices 7 2 SixC54S4InputSlices) := by
  rw [← SixC54S4Input_merge, eval_orderedMerge, ← SixC54S4Input_left_sorted, ← SixC54S4Input_right_sorted, eval_sort, eval_sort, SixC54S4Input_flat, eval_append]
end SixCertificates
