import SixC29S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC29S2InputPolynomial : Polynomial := SixC29S1OutputPolynomial
theorem SixC29S2Input_merge : orderedMerge 6188 SixC29S2InputLeftSorted SixC29S2InputRightSorted = SixC29S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC29S2Input_eval (f : ℕ →* ℝ) : eval f SixC29S2InputPolynomial = eval f (expandSlices 13 3 SixC29S2InputSlices) := by
  rw [← SixC29S2Input_merge, eval_orderedMerge, ← SixC29S2Input_left_sorted, ← SixC29S2Input_right_sorted, eval_sort, eval_sort, SixC29S2Input_flat, eval_append]
end SixCertificates
