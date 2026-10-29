import SixC04S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC04S3_cofactors : ∀ p ∈ SixC04S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC04S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC04S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixC04S2OutputPolynomial := by
  change _ = eval _ SixC04S3InputPolynomial
  rw [SixC04S3Output_eval, SixC04S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixC04S3InputSlices SixC04S3_cofactors
end SixCertificates
