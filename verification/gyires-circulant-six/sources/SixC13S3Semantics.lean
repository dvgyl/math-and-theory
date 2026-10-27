import SixC13S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC13S3_cofactors : ∀ p ∈ SixC13S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC13S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC13S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC13S2OutputPolynomial := by
  change _ = eval _ SixC13S3InputPolynomial
  rw [SixC13S3Output_eval, SixC13S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC13S3InputSlices SixC13S3_cofactors
end SixCertificates
