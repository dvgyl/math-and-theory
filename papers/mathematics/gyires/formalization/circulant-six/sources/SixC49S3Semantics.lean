import SixC49S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC49S3_cofactors : ∀ p ∈ SixC49S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC49S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC49S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC49S2OutputPolynomial := by
  change _ = eval _ SixC49S3InputPolynomial
  rw [SixC49S3Output_eval, SixC49S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC49S3InputSlices SixC49S3_cofactors
end SixCertificates
