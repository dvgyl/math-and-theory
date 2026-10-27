import SixC23S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC23S3_cofactors : ∀ p ∈ SixC23S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC23S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC23S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC23S2OutputPolynomial := by
  change _ = eval _ SixC23S3InputPolynomial
  rw [SixC23S3Output_eval, SixC23S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC23S3InputSlices SixC23S3_cofactors
end SixCertificates
