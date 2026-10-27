import SixC44S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC44S3_cofactors : ∀ p ∈ SixC44S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC44S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC44S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC44S2OutputPolynomial := by
  change _ = eval _ SixC44S3InputPolynomial
  rw [SixC44S3Output_eval, SixC44S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC44S3InputSlices SixC44S3_cofactors
end SixCertificates
