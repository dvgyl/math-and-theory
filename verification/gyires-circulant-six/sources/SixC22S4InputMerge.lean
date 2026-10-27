import SixC22S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC22S4InputPolynomial : Polynomial := SixC22S3OutputPolynomial
theorem SixC22S4Input_merge : orderedMerge 6188 SixC22S4InputLeftSorted SixC22S4InputRightSorted = SixC22S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC22S4Input_eval (f : ℕ →* ℝ) : eval f SixC22S4InputPolynomial = eval f (expandSlices 3 2 SixC22S4InputSlices) := by
  rw [← SixC22S4Input_merge, eval_orderedMerge, ← SixC22S4Input_left_sorted, ← SixC22S4Input_right_sorted, eval_sort, eval_sort, SixC22S4Input_flat, eval_append]
end SixCertificates
