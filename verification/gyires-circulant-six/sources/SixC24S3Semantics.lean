import SixC24S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC24S3_cofactors : ∀ p ∈ SixC24S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC24S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC24S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 2))) SixC24S2OutputPolynomial := by
  change _ = eval _ SixC24S3InputPolynomial
  rw [SixC24S3Output_eval, SixC24S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 2 (by decide) SixC24S3InputSlices SixC24S3_cofactors
end SixCertificates
