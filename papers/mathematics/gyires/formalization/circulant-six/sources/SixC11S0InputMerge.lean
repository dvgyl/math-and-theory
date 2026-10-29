import SixC11S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC11S0InputPolynomial : Polynomial := rawDense
theorem SixC11S0Input_merge : orderedMerge 6188 SixC11S0InputLeftSorted SixC11S0InputRightSorted = SixC11S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC11S0Input_eval (f : ℕ →* ℝ) : eval f SixC11S0InputPolynomial = eval f (expandSlices 5 11 SixC11S0InputSlices) := by
  rw [← SixC11S0Input_merge, eval_orderedMerge, ← SixC11S0Input_left_sorted, ← SixC11S0Input_right_sorted, eval_sort, eval_sort, SixC11S0Input_flat, eval_append]
end SixCertificates
