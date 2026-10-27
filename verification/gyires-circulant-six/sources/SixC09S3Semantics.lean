import SixC09S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC09S3_cofactors : ∀ p ∈ SixC09S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC09S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC09S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 1))) SixC09S2OutputPolynomial := by
  change _ = eval _ SixC09S3InputPolynomial
  rw [SixC09S3Output_eval, SixC09S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 1 (by decide) SixC09S3InputSlices SixC09S3_cofactors
end SixCertificates
