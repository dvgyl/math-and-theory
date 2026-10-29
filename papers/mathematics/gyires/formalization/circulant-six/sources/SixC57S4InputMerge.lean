import SixC57S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC57S4InputPolynomial : Polynomial := SixC57S3OutputPolynomial
theorem SixC57S4Input_merge : orderedMerge 6188 SixC57S4InputLeftSorted SixC57S4InputRightSorted = SixC57S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC57S4Input_eval (f : ℕ →* ℝ) : eval f SixC57S4InputPolynomial = eval f (expandSlices 7 2 SixC57S4InputSlices) := by
  rw [← SixC57S4Input_merge, eval_orderedMerge, ← SixC57S4Input_left_sorted, ← SixC57S4Input_right_sorted, eval_sort, eval_sort, SixC57S4Input_flat, eval_append]
end SixCertificates
