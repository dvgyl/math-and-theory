import SixC20S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC20S3_cofactors : ∀ p ∈ SixC20S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC20S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC20S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC20S2OutputPolynomial := by
  change _ = eval _ SixC20S3InputPolynomial
  rw [SixC20S3Output_eval, SixC20S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC20S3InputSlices SixC20S3_cofactors
end SixCertificates
