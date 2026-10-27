import SixC01S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC01S1InputPolynomial : Polynomial := SixC01S0OutputPolynomial
theorem SixC01S1Input_merge : orderedMerge 6188 SixC01S1InputLeftSorted SixC01S1InputRightSorted = SixC01S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC01S1Input_eval (f : ℕ →* ℝ) : eval f SixC01S1InputPolynomial = eval f (expandSlices 13 7 SixC01S1InputSlices) := by
  rw [← SixC01S1Input_merge, eval_orderedMerge, ← SixC01S1Input_left_sorted, ← SixC01S1Input_right_sorted, eval_sort, eval_sort, SixC01S1Input_flat, eval_append]
end SixCertificates
