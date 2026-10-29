import SixC51S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC51S3_cofactors : ∀ p ∈ SixC51S3InputSlices, ¬ 3 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC51S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC51S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 1 (z 1 + z 3))) SixC51S2OutputPolynomial := by
  change _ = eval _ SixC51S3InputPolynomial
  rw [SixC51S3Output_eval, SixC51S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 1 3 (by decide) SixC51S3InputSlices SixC51S3_cofactors
end SixCertificates
