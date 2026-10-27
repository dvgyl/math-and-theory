import SixC57S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC57S1InputPolynomial : Polynomial := SixC57S0OutputPolynomial
theorem SixC57S1Input_merge : orderedMerge 6188 SixC57S1InputLeftSorted SixC57S1InputRightSorted = SixC57S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC57S1Input_eval (f : ℕ →* ℝ) : eval f SixC57S1InputPolynomial = eval f (expandSlices 13 11 SixC57S1InputSlices) := by
  rw [← SixC57S1Input_merge, eval_orderedMerge, ← SixC57S1Input_left_sorted, ← SixC57S1Input_right_sorted, eval_sort, eval_sort, SixC57S1Input_flat, eval_append]
end SixCertificates
