import SixC59S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC59S3_cofactors : ∀ p ∈ SixC59S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC59S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC59S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC59S2OutputPolynomial := by
  change _ = eval _ SixC59S3InputPolynomial
  rw [SixC59S3Output_eval, SixC59S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC59S3InputSlices SixC59S3_cofactors
end SixCertificates
