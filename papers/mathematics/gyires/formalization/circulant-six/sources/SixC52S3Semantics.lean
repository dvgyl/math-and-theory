import SixC52S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC52S3_cofactors : ∀ p ∈ SixC52S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC52S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC52S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC52S2OutputPolynomial := by
  change _ = eval _ SixC52S3InputPolynomial
  rw [SixC52S3Output_eval, SixC52S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC52S3InputSlices SixC52S3_cofactors
end SixCertificates
