import SixC17S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC17S3_cofactors : ∀ p ∈ SixC17S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC17S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC17S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC17S2OutputPolynomial := by
  change _ = eval _ SixC17S3InputPolynomial
  rw [SixC17S3Output_eval, SixC17S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC17S3InputSlices SixC17S3_cofactors
end SixCertificates
