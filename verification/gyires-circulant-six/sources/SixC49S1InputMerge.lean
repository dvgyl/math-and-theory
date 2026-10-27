import SixC49S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC49S1InputPolynomial : Polynomial := SixC49S0OutputPolynomial
theorem SixC49S1Input_merge : orderedMerge 6188 SixC49S1InputLeftSorted SixC49S1InputRightSorted = SixC49S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC49S1Input_eval (f : ℕ →* ℝ) : eval f SixC49S1InputPolynomial = eval f (expandSlices 13 5 SixC49S1InputSlices) := by
  rw [← SixC49S1Input_merge, eval_orderedMerge, ← SixC49S1Input_left_sorted, ← SixC49S1Input_right_sorted, eval_sort, eval_sort, SixC49S1Input_flat, eval_append]
end SixCertificates
