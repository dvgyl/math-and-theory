import SixC16S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC16S1InputPolynomial : Polynomial := SixC16S0OutputPolynomial
theorem SixC16S1Input_merge : orderedMerge 6188 SixC16S1InputLeftSorted SixC16S1InputRightSorted = SixC16S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC16S1Input_eval (f : ℕ →* ℝ) : eval f SixC16S1InputPolynomial = eval f (expandSlices 5 13 SixC16S1InputSlices) := by
  rw [← SixC16S1Input_merge, eval_orderedMerge, ← SixC16S1Input_left_sorted, ← SixC16S1Input_right_sorted, eval_sort, eval_sort, SixC16S1Input_flat, eval_append]
end SixCertificates
