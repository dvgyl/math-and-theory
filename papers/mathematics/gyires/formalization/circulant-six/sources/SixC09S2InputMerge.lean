import SixC09S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC09S2InputPolynomial : Polynomial := SixC09S1OutputPolynomial
theorem SixC09S2Input_merge : orderedMerge 6188 SixC09S2InputLeftSorted SixC09S2InputRightSorted = SixC09S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC09S2Input_eval (f : ℕ →* ℝ) : eval f SixC09S2InputPolynomial = eval f (expandSlices 11 7 SixC09S2InputSlices) := by
  rw [← SixC09S2Input_merge, eval_orderedMerge, ← SixC09S2Input_left_sorted, ← SixC09S2Input_right_sorted, eval_sort, eval_sort, SixC09S2Input_flat, eval_append]
end SixCertificates
