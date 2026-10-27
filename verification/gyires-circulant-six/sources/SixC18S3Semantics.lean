import SixC18S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC18S3_cofactors : ∀ p ∈ SixC18S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC18S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC18S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC18S2OutputPolynomial := by
  change _ = eval _ SixC18S3InputPolynomial
  rw [SixC18S3Output_eval, SixC18S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC18S3InputSlices SixC18S3_cofactors
end SixCertificates
