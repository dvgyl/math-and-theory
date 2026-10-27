import SixC40S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC40S3_cofactors : ∀ p ∈ SixC40S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC40S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC40S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC40S2OutputPolynomial := by
  change _ = eval _ SixC40S3InputPolynomial
  rw [SixC40S3Output_eval, SixC40S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC40S3InputSlices SixC40S3_cofactors
end SixCertificates
