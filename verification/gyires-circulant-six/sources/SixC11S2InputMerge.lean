import SixC11S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC11S2InputPolynomial : Polynomial := SixC11S1OutputPolynomial
theorem SixC11S2Input_merge : orderedMerge 6188 SixC11S2InputLeftSorted SixC11S2InputRightSorted = SixC11S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC11S2Input_eval (f : ℕ →* ℝ) : eval f SixC11S2InputPolynomial = eval f (expandSlices 13 7 SixC11S2InputSlices) := by
  rw [← SixC11S2Input_merge, eval_orderedMerge, ← SixC11S2Input_left_sorted, ← SixC11S2Input_right_sorted, eval_sort, eval_sort, SixC11S2Input_flat, eval_append]
end SixCertificates
