import SixC01S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC01S2InputPolynomial : Polynomial := SixC01S1OutputPolynomial
theorem SixC01S2Input_merge : orderedMerge 6188 SixC01S2InputLeftSorted SixC01S2InputRightSorted = SixC01S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC01S2Input_eval (f : ℕ →* ℝ) : eval f SixC01S2InputPolynomial = eval f (expandSlices 7 5 SixC01S2InputSlices) := by
  rw [← SixC01S2Input_merge, eval_orderedMerge, ← SixC01S2Input_left_sorted, ← SixC01S2Input_right_sorted, eval_sort, eval_sort, SixC01S2Input_flat, eval_append]
end SixCertificates
