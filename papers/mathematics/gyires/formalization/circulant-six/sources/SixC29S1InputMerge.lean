import SixC29S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC29S1InputPolynomial : Polynomial := SixC29S0OutputPolynomial
theorem SixC29S1Input_merge : orderedMerge 6188 SixC29S1InputLeftSorted SixC29S1InputRightSorted = SixC29S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC29S1Input_eval (f : ℕ →* ℝ) : eval f SixC29S1InputPolynomial = eval f (expandSlices 11 13 SixC29S1InputSlices) := by
  rw [← SixC29S1Input_merge, eval_orderedMerge, ← SixC29S1Input_left_sorted, ← SixC29S1Input_right_sorted, eval_sort, eval_sort, SixC29S1Input_flat, eval_append]
end SixCertificates
