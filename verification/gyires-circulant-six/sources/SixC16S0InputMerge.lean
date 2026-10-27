import SixC16S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC16S0InputPolynomial : Polynomial := rawDense
theorem SixC16S0Input_merge : orderedMerge 6188 SixC16S0InputLeftSorted SixC16S0InputRightSorted = SixC16S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC16S0Input_eval (f : ℕ →* ℝ) : eval f SixC16S0InputPolynomial = eval f (expandSlices 7 5 SixC16S0InputSlices) := by
  rw [← SixC16S0Input_merge, eval_orderedMerge, ← SixC16S0Input_left_sorted, ← SixC16S0Input_right_sorted, eval_sort, eval_sort, SixC16S0Input_flat, eval_append]
end SixCertificates
