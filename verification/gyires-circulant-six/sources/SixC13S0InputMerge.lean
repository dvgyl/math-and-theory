import SixC13S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC13S0InputPolynomial : Polynomial := rawDense
theorem SixC13S0Input_merge : orderedMerge 6188 SixC13S0InputLeftSorted SixC13S0InputRightSorted = SixC13S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC13S0Input_eval (f : ℕ →* ℝ) : eval f SixC13S0InputPolynomial = eval f (expandSlices 7 13 SixC13S0InputSlices) := by
  rw [← SixC13S0Input_merge, eval_orderedMerge, ← SixC13S0Input_left_sorted, ← SixC13S0Input_right_sorted, eval_sort, eval_sort, SixC13S0Input_flat, eval_append]
end SixCertificates
