import SixC19S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC19S3_cofactors : ∀ p ∈ SixC19S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC19S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC19S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC19S2OutputPolynomial := by
  change _ = eval _ SixC19S3InputPolynomial
  rw [SixC19S3Output_eval, SixC19S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC19S3InputSlices SixC19S3_cofactors
end SixCertificates
