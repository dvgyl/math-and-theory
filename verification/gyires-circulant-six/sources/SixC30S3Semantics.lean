import SixC30S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC30S3_cofactors : ∀ p ∈ SixC30S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC30S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC30S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC30S2OutputPolynomial := by
  change _ = eval _ SixC30S3InputPolynomial
  rw [SixC30S3Output_eval, SixC30S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC30S3InputSlices SixC30S3_cofactors
end SixCertificates
