import SixC05S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC05S3_cofactors : ∀ p ∈ SixC05S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC05S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC05S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixC05S2OutputPolynomial := by
  change _ = eval _ SixC05S3InputPolynomial
  rw [SixC05S3Output_eval, SixC05S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixC05S3InputSlices SixC05S3_cofactors
end SixCertificates
