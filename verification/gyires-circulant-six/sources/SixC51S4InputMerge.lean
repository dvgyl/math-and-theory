import SixC51S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC51S4InputPolynomial : Polynomial := SixC51S3OutputPolynomial
theorem SixC51S4Input_merge : orderedMerge 6188 SixC51S4InputLeftSorted SixC51S4InputRightSorted = SixC51S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC51S4Input_eval (f : ℕ →* ℝ) : eval f SixC51S4InputPolynomial = eval f (expandSlices 7 2 SixC51S4InputSlices) := by
  rw [← SixC51S4Input_merge, eval_orderedMerge, ← SixC51S4Input_left_sorted, ← SixC51S4Input_right_sorted, eval_sort, eval_sort, SixC51S4Input_flat, eval_append]
end SixCertificates
