import SixC09S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC09S1InputPolynomial : Polynomial := SixC09S0OutputPolynomial
theorem SixC09S1Input_merge : orderedMerge 6188 SixC09S1InputLeftSorted SixC09S1InputRightSorted = SixC09S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC09S1Input_eval (f : ℕ →* ℝ) : eval f SixC09S1InputPolynomial = eval f (expandSlices 13 11 SixC09S1InputSlices) := by
  rw [← SixC09S1Input_merge, eval_orderedMerge, ← SixC09S1Input_left_sorted, ← SixC09S1Input_right_sorted, eval_sort, eval_sort, SixC09S1Input_flat, eval_append]
end SixCertificates
