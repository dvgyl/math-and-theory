import SixC38S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC38S1InputPolynomial : Polynomial := SixC38S0OutputPolynomial
theorem SixC38S1Input_merge : orderedMerge 6188 SixC38S1InputLeftSorted SixC38S1InputRightSorted = SixC38S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC38S1Input_eval (f : ℕ →* ℝ) : eval f SixC38S1InputPolynomial = eval f (expandSlices 3 7 SixC38S1InputSlices) := by
  rw [← SixC38S1Input_merge, eval_orderedMerge, ← SixC38S1Input_left_sorted, ← SixC38S1Input_right_sorted, eval_sort, eval_sort, SixC38S1Input_flat, eval_append]
end SixCertificates
