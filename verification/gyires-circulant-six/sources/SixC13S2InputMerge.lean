import SixC13S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC13S2InputPolynomial : Polynomial := SixC13S1OutputPolynomial
theorem SixC13S2Input_merge : orderedMerge 6188 SixC13S2InputLeftSorted SixC13S2InputRightSorted = SixC13S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC13S2Input_eval (f : ℕ →* ℝ) : eval f SixC13S2InputPolynomial = eval f (expandSlices 5 11 SixC13S2InputSlices) := by
  rw [← SixC13S2Input_merge, eval_orderedMerge, ← SixC13S2Input_left_sorted, ← SixC13S2Input_right_sorted, eval_sort, eval_sort, SixC13S2Input_flat, eval_append]
end SixCertificates
