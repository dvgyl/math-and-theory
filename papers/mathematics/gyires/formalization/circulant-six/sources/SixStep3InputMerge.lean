import SixStep3InputRight
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixStep3InputPolynomial : Polynomial := SixStep2OutputPolynomial
theorem SixStep3Input_merge : orderedMerge 6188 SixStep3InputLeftSorted SixStep3InputRightSorted = SixStep3InputPolynomial := by apply same_sound; decide +kernel
theorem SixStep3Input_eval (f : ℕ →* ℝ) : eval f SixStep3InputPolynomial = eval f (expandSlices 5 3 SixStep3InputSlices) := by
  rw [← SixStep3Input_merge, eval_orderedMerge, ← SixStep3Input_left_sorted, ← SixStep3Input_right_sorted, eval_sort, eval_sort, SixStep3Input_flat, eval_append]
end ChamberSix0
