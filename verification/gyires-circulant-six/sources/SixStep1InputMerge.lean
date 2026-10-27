import SixStep1InputRight
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixStep1InputPolynomial : Polynomial := SixStep0OutputPolynomial
theorem SixStep1Input_merge : orderedMerge 6188 SixStep1InputLeftSorted SixStep1InputRightSorted = SixStep1InputPolynomial := by apply same_sound; decide +kernel
theorem SixStep1Input_eval (f : ℕ →* ℝ) : eval f SixStep1InputPolynomial = eval f (expandSlices 11 7 SixStep1InputSlices) := by
  rw [← SixStep1Input_merge, eval_orderedMerge, ← SixStep1Input_left_sorted, ← SixStep1Input_right_sorted, eval_sort, eval_sort, SixStep1Input_flat, eval_append]
end ChamberSix0
