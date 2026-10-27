import SixC11S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC11S4InputPolynomial : Polynomial := SixC11S3OutputPolynomial
theorem SixC11S4Input_merge : orderedMerge 6188 SixC11S4InputLeftSorted SixC11S4InputRightSorted = SixC11S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC11S4Input_eval (f : ℕ →* ℝ) : eval f SixC11S4InputPolynomial = eval f (expandSlices 3 2 SixC11S4InputSlices) := by
  rw [← SixC11S4Input_merge, eval_orderedMerge, ← SixC11S4Input_left_sorted, ← SixC11S4Input_right_sorted, eval_sort, eval_sort, SixC11S4Input_flat, eval_append]
end SixCertificates
