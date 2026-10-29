import SixC55S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC55S3_cofactors : ∀ p ∈ SixC55S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC55S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC55S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC55S2OutputPolynomial := by
  change _ = eval _ SixC55S3InputPolynomial
  rw [SixC55S3Output_eval, SixC55S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC55S3InputSlices SixC55S3_cofactors
end SixCertificates
