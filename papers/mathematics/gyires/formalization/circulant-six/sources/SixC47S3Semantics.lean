import SixC47S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC47S3_cofactors : ∀ p ∈ SixC47S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC47S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC47S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC47S2OutputPolynomial := by
  change _ = eval _ SixC47S3InputPolynomial
  rw [SixC47S3Output_eval, SixC47S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC47S3InputSlices SixC47S3_cofactors
end SixCertificates
