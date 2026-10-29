import SixC49S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC49S4InputPolynomial : Polynomial := SixC49S3OutputPolynomial
theorem SixC49S4Input_merge : orderedMerge 6188 SixC49S4InputLeftSorted SixC49S4InputRightSorted = SixC49S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC49S4Input_eval (f : ℕ →* ℝ) : eval f SixC49S4InputPolynomial = eval f (expandSlices 7 2 SixC49S4InputSlices) := by
  rw [← SixC49S4Input_merge, eval_orderedMerge, ← SixC49S4Input_left_sorted, ← SixC49S4Input_right_sorted, eval_sort, eval_sort, SixC49S4Input_flat, eval_append]
end SixCertificates
