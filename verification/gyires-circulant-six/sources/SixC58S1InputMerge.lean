import SixC58S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC58S1InputPolynomial : Polynomial := SixC58S0OutputPolynomial
theorem SixC58S1Input_merge : orderedMerge 6188 SixC58S1InputLeftSorted SixC58S1InputRightSorted = SixC58S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC58S1Input_eval (f : ℕ →* ℝ) : eval f SixC58S1InputPolynomial = eval f (expandSlices 3 13 SixC58S1InputSlices) := by
  rw [← SixC58S1Input_merge, eval_orderedMerge, ← SixC58S1Input_left_sorted, ← SixC58S1Input_right_sorted, eval_sort, eval_sort, SixC58S1Input_flat, eval_append]
end SixCertificates
