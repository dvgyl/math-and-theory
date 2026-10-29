import SixC13S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC13S4InputPolynomial : Polynomial := SixC13S3OutputPolynomial
theorem SixC13S4Input_merge : orderedMerge 6188 SixC13S4InputLeftSorted SixC13S4InputRightSorted = SixC13S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC13S4Input_eval (f : ℕ →* ℝ) : eval f SixC13S4InputPolynomial = eval f (expandSlices 3 2 SixC13S4InputSlices) := by
  rw [← SixC13S4Input_merge, eval_orderedMerge, ← SixC13S4Input_left_sorted, ← SixC13S4Input_right_sorted, eval_sort, eval_sort, SixC13S4Input_flat, eval_append]
end SixCertificates
