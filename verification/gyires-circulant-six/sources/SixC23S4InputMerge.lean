import SixC23S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC23S4InputPolynomial : Polynomial := SixC23S3OutputPolynomial
theorem SixC23S4Input_merge : orderedMerge 6188 SixC23S4InputLeftSorted SixC23S4InputRightSorted = SixC23S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC23S4Input_eval (f : ℕ →* ℝ) : eval f SixC23S4InputPolynomial = eval f (expandSlices 3 2 SixC23S4InputSlices) := by
  rw [← SixC23S4Input_merge, eval_orderedMerge, ← SixC23S4Input_left_sorted, ← SixC23S4Input_right_sorted, eval_sort, eval_sort, SixC23S4Input_flat, eval_append]
end SixCertificates
