import SixC01S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC01S4InputPolynomial : Polynomial := SixC01S3OutputPolynomial
theorem SixC01S4Input_merge : orderedMerge 6188 SixC01S4InputLeftSorted SixC01S4InputRightSorted = SixC01S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC01S4Input_eval (f : ℕ →* ℝ) : eval f SixC01S4InputPolynomial = eval f (expandSlices 3 2 SixC01S4InputSlices) := by
  rw [← SixC01S4Input_merge, eval_orderedMerge, ← SixC01S4Input_left_sorted, ← SixC01S4Input_right_sorted, eval_sort, eval_sort, SixC01S4Input_flat, eval_append]
end SixCertificates
