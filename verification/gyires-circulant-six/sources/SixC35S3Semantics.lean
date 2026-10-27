import SixC35S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC35S3_cofactors : ∀ p ∈ SixC35S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC35S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC35S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC35S2OutputPolynomial := by
  change _ = eval _ SixC35S3InputPolynomial
  rw [SixC35S3Output_eval, SixC35S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC35S3InputSlices SixC35S3_cofactors
end SixCertificates
