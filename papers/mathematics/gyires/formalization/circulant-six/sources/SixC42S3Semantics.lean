import SixC42S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC42S3_cofactors : ∀ p ∈ SixC42S3InputSlices, ¬ 13 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC42S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC42S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 5 (z 5 + z 2))) SixC42S2OutputPolynomial := by
  change _ = eval _ SixC42S3InputPolynomial
  rw [SixC42S3Output_eval, SixC42S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 5 2 (by decide) SixC42S3InputSlices SixC42S3_cofactors
end SixCertificates
