import SixC15S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC15S3_cofactors : ∀ p ∈ SixC15S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC15S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC15S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC15S2OutputPolynomial := by
  change _ = eval _ SixC15S3InputPolynomial
  rw [SixC15S3Output_eval, SixC15S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC15S3InputSlices SixC15S3_cofactors
end SixCertificates
