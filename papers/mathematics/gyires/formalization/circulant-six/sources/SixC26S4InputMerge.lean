import SixC26S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC26S4InputPolynomial : Polynomial := SixC26S3OutputPolynomial
theorem SixC26S4Input_merge : orderedMerge 6188 SixC26S4InputLeftSorted SixC26S4InputRightSorted = SixC26S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC26S4Input_eval (f : ℕ →* ℝ) : eval f SixC26S4InputPolynomial = eval f (expandSlices 5 2 SixC26S4InputSlices) := by
  rw [← SixC26S4Input_merge, eval_orderedMerge, ← SixC26S4Input_left_sorted, ← SixC26S4Input_right_sorted, eval_sort, eval_sort, SixC26S4Input_flat, eval_append]
end SixCertificates
