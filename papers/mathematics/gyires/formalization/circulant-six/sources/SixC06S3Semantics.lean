import SixC06S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC06S3_cofactors : ∀ p ∈ SixC06S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC06S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC06S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC06S2OutputPolynomial := by
  change _ = eval _ SixC06S3InputPolynomial
  rw [SixC06S3Output_eval, SixC06S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC06S3InputSlices SixC06S3_cofactors
end SixCertificates
