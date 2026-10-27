import SixC31S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC31S3_cofactors : ∀ p ∈ SixC31S3InputSlices, ¬ 7 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC31S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC31S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 3 (z 3 + z 2))) SixC31S2OutputPolynomial := by
  change _ = eval _ SixC31S3InputPolynomial
  rw [SixC31S3Output_eval, SixC31S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 3 2 (by decide) SixC31S3InputSlices SixC31S3_cofactors
end SixCertificates
