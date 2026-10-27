import SixC43S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC43S3_cofactors : ∀ p ∈ SixC43S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC43S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC43S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC43S2OutputPolynomial := by
  change _ = eval _ SixC43S3InputPolynomial
  rw [SixC43S3Output_eval, SixC43S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC43S3InputSlices SixC43S3_cofactors
end SixCertificates
