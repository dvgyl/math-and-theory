import SixC15S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC15S4InputPolynomial : Polynomial := SixC15S3OutputPolynomial
theorem SixC15S4Input_merge : orderedMerge 6188 SixC15S4InputLeftSorted SixC15S4InputRightSorted = SixC15S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC15S4Input_eval (f : ℕ →* ℝ) : eval f SixC15S4InputPolynomial = eval f (expandSlices 3 2 SixC15S4InputSlices) := by
  rw [← SixC15S4Input_merge, eval_orderedMerge, ← SixC15S4Input_left_sorted, ← SixC15S4Input_right_sorted, eval_sort, eval_sort, SixC15S4Input_flat, eval_append]
end SixCertificates
