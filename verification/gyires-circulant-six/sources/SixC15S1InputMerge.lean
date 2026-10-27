import SixC15S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC15S1InputPolynomial : Polynomial := SixC15S0OutputPolynomial
theorem SixC15S1Input_merge : orderedMerge 6188 SixC15S1InputLeftSorted SixC15S1InputRightSorted = SixC15S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC15S1Input_eval (f : ℕ →* ℝ) : eval f SixC15S1InputPolynomial = eval f (expandSlices 13 7 SixC15S1InputSlices) := by
  rw [← SixC15S1Input_merge, eval_orderedMerge, ← SixC15S1Input_left_sorted, ← SixC15S1Input_right_sorted, eval_sort, eval_sort, SixC15S1Input_flat, eval_append]
end SixCertificates
