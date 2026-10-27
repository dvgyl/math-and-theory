import SixC33S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC33S2InputPolynomial : Polynomial := SixC33S1OutputPolynomial
theorem SixC33S2Input_merge : orderedMerge 6188 SixC33S2InputLeftSorted SixC33S2InputRightSorted = SixC33S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC33S2Input_eval (f : ℕ →* ℝ) : eval f SixC33S2InputPolynomial = eval f (expandSlices 11 7 SixC33S2InputSlices) := by
  rw [← SixC33S2Input_merge, eval_orderedMerge, ← SixC33S2Input_left_sorted, ← SixC33S2Input_right_sorted, eval_sort, eval_sort, SixC33S2Input_flat, eval_append]
end SixCertificates
