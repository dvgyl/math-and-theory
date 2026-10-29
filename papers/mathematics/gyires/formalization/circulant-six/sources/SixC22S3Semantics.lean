import SixC22S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC22S3_cofactors : ∀ p ∈ SixC22S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC22S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC22S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC22S2OutputPolynomial := by
  change _ = eval _ SixC22S3InputPolynomial
  rw [SixC22S3Output_eval, SixC22S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC22S3InputSlices SixC22S3_cofactors
end SixCertificates
