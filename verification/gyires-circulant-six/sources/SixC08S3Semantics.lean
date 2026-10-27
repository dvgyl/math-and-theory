import SixC08S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC08S3_cofactors : ∀ p ∈ SixC08S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC08S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC08S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC08S2OutputPolynomial := by
  change _ = eval _ SixC08S3InputPolynomial
  rw [SixC08S3Output_eval, SixC08S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC08S3InputSlices SixC08S3_cofactors
end SixCertificates
