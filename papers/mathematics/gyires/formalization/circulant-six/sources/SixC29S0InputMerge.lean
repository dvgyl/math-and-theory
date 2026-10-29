import SixC29S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC29S0InputPolynomial : Polynomial := rawDense
theorem SixC29S0Input_merge : orderedMerge 6188 SixC29S0InputLeftSorted SixC29S0InputRightSorted = SixC29S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC29S0Input_eval (f : ℕ →* ℝ) : eval f SixC29S0InputPolynomial = eval f (expandSlices 7 11 SixC29S0InputSlices) := by
  rw [← SixC29S0Input_merge, eval_orderedMerge, ← SixC29S0Input_left_sorted, ← SixC29S0Input_right_sorted, eval_sort, eval_sort, SixC29S0Input_flat, eval_append]
end SixCertificates
