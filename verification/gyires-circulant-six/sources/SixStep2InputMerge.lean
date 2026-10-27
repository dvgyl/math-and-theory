import SixStep2InputRight
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixStep2InputPolynomial : Polynomial := SixStep1OutputPolynomial
theorem SixStep2Input_merge : orderedMerge 6188 SixStep2InputLeftSorted SixStep2InputRightSorted = SixStep2InputPolynomial := by apply same_sound; decide +kernel
theorem SixStep2Input_eval (f : ℕ →* ℝ) : eval f SixStep2InputPolynomial = eval f (expandSlices 7 5 SixStep2InputSlices) := by
  rw [← SixStep2Input_merge, eval_orderedMerge, ← SixStep2Input_left_sorted, ← SixStep2Input_right_sorted, eval_sort, eval_sort, SixStep2Input_flat, eval_append]
end ChamberSix0
