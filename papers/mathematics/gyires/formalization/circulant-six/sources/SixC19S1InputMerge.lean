import SixC19S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC19S1InputPolynomial : Polynomial := SixC19S0OutputPolynomial
theorem SixC19S1Input_merge : orderedMerge 6188 SixC19S1InputLeftSorted SixC19S1InputRightSorted = SixC19S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC19S1Input_eval (f : ℕ →* ℝ) : eval f SixC19S1InputPolynomial = eval f (expandSlices 11 5 SixC19S1InputSlices) := by
  rw [← SixC19S1Input_merge, eval_orderedMerge, ← SixC19S1Input_left_sorted, ← SixC19S1Input_right_sorted, eval_sort, eval_sort, SixC19S1Input_flat, eval_append]
end SixCertificates
