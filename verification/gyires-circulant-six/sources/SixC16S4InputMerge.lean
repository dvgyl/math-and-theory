import SixC16S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC16S4InputPolynomial : Polynomial := SixC16S3OutputPolynomial
theorem SixC16S4Input_merge : orderedMerge 6188 SixC16S4InputLeftSorted SixC16S4InputRightSorted = SixC16S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC16S4Input_eval (f : ℕ →* ℝ) : eval f SixC16S4InputPolynomial = eval f (expandSlices 3 2 SixC16S4InputSlices) := by
  rw [← SixC16S4Input_merge, eval_orderedMerge, ← SixC16S4Input_left_sorted, ← SixC16S4Input_right_sorted, eval_sort, eval_sort, SixC16S4Input_flat, eval_append]
end SixCertificates
