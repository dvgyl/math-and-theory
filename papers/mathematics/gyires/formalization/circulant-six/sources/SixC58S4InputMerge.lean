import SixC58S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC58S4InputPolynomial : Polynomial := SixC58S3OutputPolynomial
theorem SixC58S4Input_merge : orderedMerge 6188 SixC58S4InputLeftSorted SixC58S4InputRightSorted = SixC58S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC58S4Input_eval (f : ℕ →* ℝ) : eval f SixC58S4InputPolynomial = eval f (expandSlices 7 2 SixC58S4InputSlices) := by
  rw [← SixC58S4Input_merge, eval_orderedMerge, ← SixC58S4Input_left_sorted, ← SixC58S4Input_right_sorted, eval_sort, eval_sort, SixC58S4Input_flat, eval_append]
end SixCertificates
