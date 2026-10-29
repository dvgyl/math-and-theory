import SixC03S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC03S3_cofactors : ∀ p ∈ SixC03S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC03S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC03S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixC03S2OutputPolynomial := by
  change _ = eval _ SixC03S3InputPolynomial
  rw [SixC03S3Output_eval, SixC03S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixC03S3InputSlices SixC03S3_cofactors
end SixCertificates
