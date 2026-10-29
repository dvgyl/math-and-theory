import SixC39S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC39S3_cofactors : ∀ p ∈ SixC39S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC39S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC39S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC39S2OutputPolynomial := by
  change _ = eval _ SixC39S3InputPolynomial
  rw [SixC39S3Output_eval, SixC39S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC39S3InputSlices SixC39S3_cofactors
end SixCertificates
