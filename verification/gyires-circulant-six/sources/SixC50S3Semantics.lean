import SixC50S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC50S3_cofactors : ∀ p ∈ SixC50S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC50S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC50S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC50S2OutputPolynomial := by
  change _ = eval _ SixC50S3InputPolynomial
  rw [SixC50S3Output_eval, SixC50S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC50S3InputSlices SixC50S3_cofactors
end SixCertificates
