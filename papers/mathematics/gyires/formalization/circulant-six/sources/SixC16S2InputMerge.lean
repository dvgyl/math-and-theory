import SixC16S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC16S2InputPolynomial : Polynomial := SixC16S1OutputPolynomial
theorem SixC16S2Input_merge : orderedMerge 6188 SixC16S2InputLeftSorted SixC16S2InputRightSorted = SixC16S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC16S2Input_eval (f : ℕ →* ℝ) : eval f SixC16S2InputPolynomial = eval f (expandSlices 13 11 SixC16S2InputSlices) := by
  rw [← SixC16S2Input_merge, eval_orderedMerge, ← SixC16S2Input_left_sorted, ← SixC16S2Input_right_sorted, eval_sort, eval_sort, SixC16S2Input_flat, eval_append]
end SixCertificates
