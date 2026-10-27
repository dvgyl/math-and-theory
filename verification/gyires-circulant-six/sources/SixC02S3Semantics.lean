import SixC02S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC02S3_cofactors : ∀ p ∈ SixC02S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC02S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC02S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 1))) SixC02S2OutputPolynomial := by
  change _ = eval _ SixC02S3InputPolynomial
  rw [SixC02S3Output_eval, SixC02S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 1 (by decide) SixC02S3InputSlices SixC02S3_cofactors
end SixCertificates
