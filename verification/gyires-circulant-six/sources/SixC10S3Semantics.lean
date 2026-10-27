import SixC10S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC10S3_cofactors : ∀ p ∈ SixC10S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC10S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC10S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC10S2OutputPolynomial := by
  change _ = eval _ SixC10S3InputPolynomial
  rw [SixC10S3Output_eval, SixC10S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC10S3InputSlices SixC10S3_cofactors
end SixCertificates
