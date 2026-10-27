import SixC13S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC13S1InputPolynomial : Polynomial := SixC13S0OutputPolynomial
theorem SixC13S1Input_merge : orderedMerge 6188 SixC13S1InputLeftSorted SixC13S1InputRightSorted = SixC13S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC13S1Input_eval (f : ℕ →* ℝ) : eval f SixC13S1InputPolynomial = eval f (expandSlices 13 5 SixC13S1InputSlices) := by
  rw [← SixC13S1Input_merge, eval_orderedMerge, ← SixC13S1Input_left_sorted, ← SixC13S1Input_right_sorted, eval_sort, eval_sort, SixC13S1Input_flat, eval_append]
end SixCertificates
