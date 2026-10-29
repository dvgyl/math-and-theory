import SixC33S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC33S1InputPolynomial : Polynomial := SixC33S0OutputPolynomial
theorem SixC33S1Input_merge : orderedMerge 6188 SixC33S1InputLeftSorted SixC33S1InputRightSorted = SixC33S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC33S1Input_eval (f : ℕ →* ℝ) : eval f SixC33S1InputPolynomial = eval f (expandSlices 13 11 SixC33S1InputSlices) := by
  rw [← SixC33S1Input_merge, eval_orderedMerge, ← SixC33S1Input_left_sorted, ← SixC33S1Input_right_sorted, eval_sort, eval_sort, SixC33S1Input_flat, eval_append]
end SixCertificates
