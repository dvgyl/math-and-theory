import SixC33S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC33S4InputPolynomial : Polynomial := SixC33S3OutputPolynomial
theorem SixC33S4Input_merge : orderedMerge 6188 SixC33S4InputLeftSorted SixC33S4InputRightSorted = SixC33S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC33S4Input_eval (f : ℕ →* ℝ) : eval f SixC33S4InputPolynomial = eval f (expandSlices 5 2 SixC33S4InputSlices) := by
  rw [← SixC33S4Input_merge, eval_orderedMerge, ← SixC33S4Input_left_sorted, ← SixC33S4Input_right_sorted, eval_sort, eval_sort, SixC33S4Input_flat, eval_append]
end SixCertificates
