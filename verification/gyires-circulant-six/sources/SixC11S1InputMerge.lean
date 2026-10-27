import SixC11S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC11S1InputPolynomial : Polynomial := SixC11S0OutputPolynomial
theorem SixC11S1Input_merge : orderedMerge 6188 SixC11S1InputLeftSorted SixC11S1InputRightSorted = SixC11S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC11S1Input_eval (f : ℕ →* ℝ) : eval f SixC11S1InputPolynomial = eval f (expandSlices 11 13 SixC11S1InputSlices) := by
  rw [← SixC11S1Input_merge, eval_orderedMerge, ← SixC11S1Input_left_sorted, ← SixC11S1Input_right_sorted, eval_sort, eval_sort, SixC11S1Input_flat, eval_append]
end SixCertificates
