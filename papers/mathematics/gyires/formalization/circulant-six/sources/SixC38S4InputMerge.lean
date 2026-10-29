import SixC38S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC38S4InputPolynomial : Polynomial := SixC38S3OutputPolynomial
theorem SixC38S4Input_merge : orderedMerge 6188 SixC38S4InputLeftSorted SixC38S4InputRightSorted = SixC38S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC38S4Input_eval (f : ℕ →* ℝ) : eval f SixC38S4InputPolynomial = eval f (expandSlices 5 2 SixC38S4InputSlices) := by
  rw [← SixC38S4Input_merge, eval_orderedMerge, ← SixC38S4Input_left_sorted, ← SixC38S4Input_right_sorted, eval_sort, eval_sort, SixC38S4Input_flat, eval_append]
end SixCertificates
