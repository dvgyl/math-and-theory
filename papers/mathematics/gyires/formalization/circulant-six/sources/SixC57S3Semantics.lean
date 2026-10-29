import SixC57S3OutputMerge
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem SixC57S3_cofactors : ∀ p ∈ SixC57S3InputSlices, ¬ 5 ∣ p.1 := by
  apply noFactor_sound
  decide +kernel
theorem SixC57S3_eval (z : Fin 6 → ℝ) : eval (primeEvaluation primes z) SixC57S3OutputPolynomial = eval (primeEvaluation primes (Function.update z 2 (z 2 + z 3))) SixC57S2OutputPolynomial := by
  change _ = eval _ SixC57S3InputPolynomial
  rw [SixC57S3Output_eval, SixC57S3Input_eval]
  exact eval_shiftSlices_update primes primes_prime primes_injective z 2 3 (by decide) SixC57S3InputSlices SixC57S3_cofactors
end SixCertificates
