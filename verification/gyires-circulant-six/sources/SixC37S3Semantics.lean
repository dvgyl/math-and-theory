import SixC37S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC37S3_cofactors : ∀ p ∈ SixC37S3InputSlices, ¬ 11 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC37S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC37S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 4 (z 4 + z 2))) SixC37S2OutputPolynomial := by
  change _ = eval _ SixC37S3InputPolynomial
  rw [SixC37S3Output_eval, SixC37S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 4 2 (by decide) SixC37S3InputSlices SixC37S3_cofactors
end SixCertificates
