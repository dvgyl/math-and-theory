import SixC36S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC36S3_cofactors : ∀ p ∈ SixC36S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC36S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC36S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC36S2OutputPolynomial := by
  change _ = eval _ SixC36S3InputPolynomial
  rw [SixC36S3Output_eval, SixC36S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC36S3InputSlices SixC36S3_cofactors
end SixCertificates
