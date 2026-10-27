import SixC02S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC02S4InputPolynomial : Polynomial := SixC02S3OutputPolynomial
theorem SixC02S4Input_merge : orderedMerge 6188 SixC02S4InputLeftSorted SixC02S4InputRightSorted = SixC02S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC02S4Input_eval (f : ℕ →* ℝ) : eval f SixC02S4InputPolynomial = eval f (expandSlices 3 2 SixC02S4InputSlices) := by
  rw [← SixC02S4Input_merge, eval_orderedMerge, ← SixC02S4Input_left_sorted, ← SixC02S4Input_right_sorted, eval_sort, eval_sort, SixC02S4Input_flat, eval_append]
end SixCertificates
