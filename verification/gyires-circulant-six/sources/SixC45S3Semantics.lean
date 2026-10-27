import SixC45S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC45S3_cofactors : ∀ p ∈ SixC45S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC45S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC45S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC45S2OutputPolynomial := by
  change _ = eval _ SixC45S3InputPolynomial
  rw [SixC45S3Output_eval, SixC45S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC45S3InputSlices SixC45S3_cofactors
end SixCertificates
