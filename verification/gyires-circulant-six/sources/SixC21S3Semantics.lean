import SixC21S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC21S3_cofactors : ∀ p ∈ SixC21S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC21S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC21S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 1))) SixC21S2OutputPolynomial := by
  change _ = eval _ SixC21S3InputPolynomial
  rw [SixC21S3Output_eval, SixC21S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 1 (by decide) SixC21S3InputSlices SixC21S3_cofactors
end SixCertificates
