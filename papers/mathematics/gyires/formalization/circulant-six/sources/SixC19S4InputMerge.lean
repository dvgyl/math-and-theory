import SixC19S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC19S4InputPolynomial : Polynomial := SixC19S3OutputPolynomial
theorem SixC19S4Input_merge : orderedMerge 6188 SixC19S4InputLeftSorted SixC19S4InputRightSorted = SixC19S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC19S4Input_eval (f : ℕ →* ℝ) : eval f SixC19S4InputPolynomial = eval f (expandSlices 3 2 SixC19S4InputSlices) := by
  rw [← SixC19S4Input_merge, eval_orderedMerge, ← SixC19S4Input_left_sorted, ← SixC19S4Input_right_sorted, eval_sort, eval_sort, SixC19S4Input_flat, eval_append]
end SixCertificates
