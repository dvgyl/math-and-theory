import SixC16S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC16S3_cofactors : ∀ p ∈ SixC16S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC16S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC16S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 1))) SixC16S2OutputPolynomial := by
  change _ = eval _ SixC16S3InputPolynomial
  rw [SixC16S3Output_eval, SixC16S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 1 (by decide) SixC16S3InputSlices SixC16S3_cofactors
end SixCertificates
