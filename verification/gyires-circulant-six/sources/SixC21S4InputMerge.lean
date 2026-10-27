import SixC21S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC21S4InputPolynomial : Polynomial := SixC21S3OutputPolynomial
theorem SixC21S4Input_merge : orderedMerge 6188 SixC21S4InputLeftSorted SixC21S4InputRightSorted = SixC21S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC21S4Input_eval (f : ℕ →* ℝ) : eval f SixC21S4InputPolynomial = eval f (expandSlices 3 2 SixC21S4InputSlices) := by
  rw [← SixC21S4Input_merge, eval_orderedMerge, ← SixC21S4Input_left_sorted, ← SixC21S4Input_right_sorted, eval_sort, eval_sort, SixC21S4Input_flat, eval_append]
end SixCertificates
