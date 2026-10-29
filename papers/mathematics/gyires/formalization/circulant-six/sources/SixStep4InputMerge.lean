import SixStep4InputRight
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixStep4InputPolynomial : Polynomial := SixStep3OutputPolynomial
theorem SixStep4Input_merge : orderedMerge 6188 SixStep4InputLeftSorted SixStep4InputRightSorted = SixStep4InputPolynomial := by apply same_sound; decide +kernel
theorem SixStep4Input_eval (f : ℕ →* ℝ) : eval f SixStep4InputPolynomial = eval f (expandSlices 3 2 SixStep4InputSlices) := by
  rw [← SixStep4Input_merge, eval_orderedMerge, ← SixStep4Input_left_sorted, ← SixStep4Input_right_sorted, eval_sort, eval_sort, SixStep4Input_flat, eval_append]
end ChamberSix0
