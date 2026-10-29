import SixC38S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC38S3_cofactors : ∀ p ∈ SixC38S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC38S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC38S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC38S2OutputPolynomial := by
  change _ = eval _ SixC38S3InputPolynomial
  rw [SixC38S3Output_eval, SixC38S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC38S3InputSlices SixC38S3_cofactors
end SixCertificates
