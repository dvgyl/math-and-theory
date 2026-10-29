import SixC25S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC25S3_cofactors : ∀ p ∈ SixC25S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC25S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC25S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 2))) SixC25S2OutputPolynomial := by
  change _ = eval _ SixC25S3InputPolynomial
  rw [SixC25S3Output_eval, SixC25S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 2 (by decide) SixC25S3InputSlices SixC25S3_cofactors
end SixCertificates
