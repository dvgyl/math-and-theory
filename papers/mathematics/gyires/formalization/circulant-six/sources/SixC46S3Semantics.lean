import SixC46S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC46S3_cofactors : ∀ p ∈ SixC46S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC46S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC46S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC46S2OutputPolynomial := by
  change _ = eval _ SixC46S3InputPolynomial
  rw [SixC46S3Output_eval, SixC46S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC46S3InputSlices SixC46S3_cofactors
end SixCertificates
